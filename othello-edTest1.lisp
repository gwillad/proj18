;;;; -*- Mode: Lisp; Syntax: Common-Lisp -*-
;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig

;;;; File othello.lisp: An othello monitor, with all strategies
;;;; up to and including section 18.8

;;; One bug fix by Alberto Segre, segre@cs.cornell.edu, March 1993.
(load "auxfns")

(defun cross-product (fn xlist ylist)
  "Return a list of all (fn x y) values."
  (mappend #'(lambda (y)
               (mapcar #'(lambda (x) (funcall fn x y))
                       xlist))
           ylist))

(defconstant all-directions '(-11 -10 -9 -1 1 9 10 11))

(defconstant empty 0 "An empty square")
(defconstant black 1 "A black piece")
(defconstant white 2 "A white piece")
(defconstant outer 3 "Marks squares outside the 8x8 board")

(deftype piece () `(integer ,empty ,outer))

(defun name-of (piece) (char ".@O?" piece))

(defun opponent (player) (if (eql player black) white black))

(deftype board () '(simple-array piece (64)))

(defun bref (board square) (aref board square))
(defsetf bref (board square) (val) 
  `(setf (aref ,board ,square) ,val))

(defun copy-board (board)
  (copy-seq board))

(defun col->num-help (row col board)
  (if (eql (bref board (+ row col)) empty)
      (+ row col)
    (col->num-help (- row 9) col board)))

(defun col->num (col board)
  "Convert from column number to numeric square notation."
  (col->num-help 54 col board))

(defun num->col (num)
  "Convert from number to column number."
  (mod num 9))

(defconstant all-squares
  (loop for i from 10 to 61 when (<= 1 (mod i 9) 7) collect i))

(defun initial-board ()
  "Return a board, empty except for four pieces in the middle."
  ;; Boards are 72-element vectors, with elements 10-61 used,
  ;; and the others marked with the sentinel OUTER.
  (let ((board (make-array 72 :element-type 'piece
                           :initial-element outer)))
    (dolist (square all-squares)
      (setf (bref board square) empty))
    board))

(defun count-difference (player board)
  "Count player's pieces minus opponent's pieces."
  (- (count player board)
     (count (opponent player) board)))

(defun how-many (start board dir num)
  (if (eql (bref board (+ start dir)) (bref board start))
      (how-many (+ start dir) board dir (+ 1 num))
    num))

(defun count-in-row (player total start board)
  "Count the number of pieces the player has in a row."
;  (princ "In count-in-row. Looking at pos: ")(princ start)(terpri)
  (if (eql start 62)
      total
    (if (eql (bref board start) player)
	(let ((in-a-row (max
			(how-many start board 1 1)
			(how-many start board 8 1)
			(how-many start board 9 1)
			(how-many start board 10 1))))
	  (count-in-row player (+ total (* in-a-row in-a-row))
			(+ start 1) board))
      (count-in-row player total (+ start 1) board))))

(defun evaluation-fn (player board)
  "Returns sum of each connected string on board squared
   ie 2 in a row is worth 4, 3 is worth 9, etc"
  (count-in-row player 0 10 board))

(defun valid-p (move)
  "Valid moves are columns 1-7 as long as the column isn't full."
  (and (integerp move) (<= 1 move 7)))

(defun legal-p (move board)
  "A Legal move must be into an empty square,
   and with no empty squares below it."
  (eql (bref board (+ move 9)) empty))

(defun make-move (move player board)
  "Update board to reflect move by player"
  (if (> move 7)
      (setf (bref board move) player)
    (setf (bref board (col->num move board)) player))
  board)
  

(defun find-bracketing-piece (square player board dir)
  "Return the square number of the bracketing piece."
  (cond ((eql (bref board square) player) square)
        ((eql (bref board square) (opponent player))
         (find-bracketing-piece (+ square dir) player board dir))
        (t nil)))

(defun next-to-play (board previous-player print)
  "Compute the player to move next, or NIL if nobody can move."
  (let ((opp (opponent previous-player)))
    (cond ((any-legal-move? opp board) opp)
          ((any-legal-move? previous-player board) 
           (when print
             (format t "~&~c has no moves and must pass."
                     (name-of opp)))
           previous-player)
          (t nil))))

(defun any-legal-move? (player board)
  "Does player have any legal moves in this position?"
  (some #'(lambda (move) (legal-p move board))
        all-squares))

(defun random-strategy (player board)
  "Make any legal move."
  (dbg-indent :othello 0 "Choosing randomly from: ~a"  (legal-moves board))
  
  (random-elt (legal-moves board)))

(defun legal-moves (board)
  "Returns a list of legal moves for player"
  (loop for move from 1 to 7
	when (legal-p move board) collect move))

(defun maximize-difference (player board)
  "A strategy that maximizes the difference in pieces."
  (funcall (maximizer #'count-difference) player board))

(defun maximizer (eval-fn)
  "Return a strategy that will consider every legal move,
  apply EVAL-FN to each resulting board, and choose 
  the move for which EVAL-FN returns the best score.
  FN takes two arguments: the player-to-move and board"
  #'(lambda (player board)
      (princ "In maximizer...")(terpri)
      (princ "board: ")(princ board)(terpri)
      (let* ((moves (legal-moves board))
             (scores (mapcar 
		      #'(lambda (move)
			  (funcall 
			   eval-fn 
			   player 
			   (make-move 
			    (col->num move board) 
			    player 
			    (copy-board board))))
		      moves))
             (best  (apply #'max scores)))
        (elt moves (position best scores)))))

(defparameter *weights*
  '#(0 0 0 0 0 0 0 0 0
     0 1 1 1 1 1 1 1 0
     0 1 1 1 1 1 1 1 0
     0 1 1 1 1 1 1 1 0
     0 1 1 1 1 1 1 1 0
     0 1 1 1 1 1 1 1 0
     0 1 1 1 1 1 1 1 0
     0 0 0 0 0 0 0 0 0))

(defun weighted-squares (player board)
  "Sum of the weights of player's squares minus opponent's."
  (let ((opp (opponent player)))
    (loop for i in all-squares
          when (eql (bref board i) player) 
          sum (aref *weights* i)
          when (eql (bref board i) opp)
          sum (- (aref *weights* i)))))

(defconstant winning-value most-positive-fixnum)
(defconstant losing-value  most-negative-fixnum)

(defun final-value (player board)
  "Is this a win, loss, or draw for player?"
  (case (signum (count-difference player board))
    (-1 losing-value)
    ( 0 0)
    (+1 winning-value)))

(defun minimax (player board ply eval-fn)
  "Find the best move, for PLAYER, according to EVAL-FN,
  searching PLY levels deep and backing up values."
  (if (= ply 0)
      (funcall eval-fn player board)
      (let ((moves (legal-moves board)))
        (if (null moves)
            (if (any-legal-move? (opponent player) board)
                (- (minimax (opponent player) board
                            (- ply 1) eval-fn))
                (final-value player board))
            (let ((best-move nil)
                  (best-val nil))
              (dolist (move moves)
                (let* ((board2 (make-move move player
                                          (copy-board board)))
                       (val (- (minimax
                                 (opponent player) board2
                                 (- ply 1) eval-fn))))
                  (when (or (null best-val)
                            (> val best-val))
                    (setf best-val val)
                    (setf best-move move))))
              (values best-val best-move))))))

(defun minimax-searcher (ply eval-fn)
  "A strategy that searches PLY levels and then uses EVAL-FN."
  #'(lambda (player board)
      (multiple-value-bind (value move)
          (minimax player board ply eval-fn) 
        (declare (ignore value))
        move)))

;(defun alpha-beta (player board achievable cutoff ply eval-fn)
;  "Find the best move, for PLAYER, according to EVAL-FN,
;  searching PLY levels deep and backing up values,
;  using cutoffs whenever possible."
;  (if (= ply 0)
;      (funcall eval-fn player board)
;      (let ((moves (legal-moves board)))
;            (if (any-legal-move? (opponent player) board)
;                (- (alpha-beta (opponent player) board
;                               (- cutoff) (- achievable)
;                               (- ply 1) eval-fn))
;                (final-value player board))
;            (let ((best-move (first moves)))
;              (loop for move in moves do
;                (let* ((board2 (make-move move player
;                                          (copy-board board)))
;                       (val (- (alpha-beta
;                                 (opponent player) board2
;                                 (- cutoff) (- achievable)
;                                 (- ply 1) eval-fn))))
;                  (when (> val achievable)
;                    (setf achievable val)
;                    (setf best-move move)))
;                until (>= achievable cutoff))
;              (values achievable best-move))))))

;(defun alpha-beta-searcher (depth eval-fn)
;  "A strategy that searches to DEPTH and then uses EVAL-FN."
;  #'(lambda (player board)
;      (multiple-value-bind (value move)
;          (alpha-beta player board losing-value winning-value
;                      depth eval-fn) 
;        (declare (ignore value))
;        move)))

(defun modified-weighted-squares (player board)
  "Like WEIGHTED-SQUARES, but don't take off for moving
  near an occupied corner."
  (let ((w (weighted-squares player board)))
    (dolist (corner '(10 16 55 61))
      (when (not (eql (bref board corner) empty))
        (dolist (c (neighbors corner))
          (when (not (eql (bref board c) empty))
            (incf w (* (- 5 (aref *weights* c))
                       (if (eql (bref board c) player)
                           +1 -1)))))))
    w))

(let ((neighbor-table (make-array 72 :initial-element nil)))
  ;; Initialize the neighbor table
  (dolist (square all-squares)
    (dolist (dir all-directions)
      (if (valid-p (+ square dir))
          (push (+ square dir)
                (aref neighbor-table square)))))

  (defun neighbors (square)
    "Return a list of all squares adjacent to a square."
    (aref neighbor-table square)))


;;; allows for early termination by entering a move of: resign
(defun human (player board)
  "A human player for the game of Othello"
  (format t "~&~c to move ~a: " (name-of player)
          (legal-moves board))
  (read))


(defun find-four (start board dir num-left)
  (if (eql num-left 0)
      t
    (if (eql (bref board start) (bref board (+ start dir)))
	(find-four (+ start dir) board dir (- num-left 1))
      nil)))

(defun winner (start board)
  (if (eql start 62)
      nil
    (if (or (eql (bref board start) black) (eql (bref board start) white))
	(if (or
	     (find-four start board -10 3)
	     (find-four start board -9 3)
	     (find-four start board -8 3)
	     (find-four start board -1 3)
	     (find-four start board 1 3)
	     (find-four start board 8 3)
	     (find-four start board 9 3)
	     (find-four start board 10 3))
	    (bref board start)
	  (winner (+ start 1) board))
      (winner (+ start 1) board))
    ))

(defvar *move-number* 1 "The number of the move to be played")

(defun othello (bl-strategy wh-strategy 
                &optional (print t) (minutes 30))
  "Play a game of othello.  Return the score, where a positive
  difference means black, the first player, wins."
  (let ((board (initial-board))
        (clock (make-array (+ 1 (max black white))
                           :initial-element 
                           (* minutes 60 
                              internal-time-units-per-second))))
    (catch 'game-over
      (loop for *move-number* from 1
            for player = black then (next-to-play board player print)
            for strategy = (if (eql player black) 
                               bl-strategy
                               wh-strategy)
            until (or (not (null (winner 10 board))) (null player))
            do (get-move strategy player board print clock))
      (when print
        (format t "~&The game is over.  Final result: ")
        (print-board board clock)
	(princ "The winner is player ")
	(princ (winner 10 board))(terpri))
      (count-difference black board))))

(defvar *clock* (make-array 3) "A copy of the game clock")
(defvar *board* (initial-board) "A copy of the game board")

(defun get-move (strategy player board print clock)
  "Call the player's strategy function to get a move.
  Keep calling until a legal move is made."
  ;; Note we don't pass the strategy function the REAL board.
  ;; If we did, it could cheat by changing the pieces on the board.
  (princ "In get-move...")(terpri)
  (when print (print-board board clock))
  (replace *clock* clock)
  (let* ((t0 (get-internal-real-time))
         (move (funcall strategy player (replace *board* board)))
         (t1 (get-internal-real-time)))
    (decf (elt clock player) (- t1 t0))
    (cond
      ((< (elt clock player) 0)
       (format t "~&~c has no time left and forfeits."
               (name-of player))
       (THROW 'game-over (if (eql player black) -42 42)))
      ((eq move 'resign)
       (THROW 'game-over (if (eql player black) -42 42)))
      ((and (valid-p move) (legal-p move board))
       (when print
         (format t "~&~c moves to ~a." 
                 (name-of player) move))
       (make-move (col->num move board) player board))
      (t (warn "Illegal move: ~a" (num->col move))
         (get-move strategy player board print clock)))))

(defun print-board (&optional (board *board*) clock)
  "Print a board, along with some statistics."
  ;; First print the header and the current score
  (format t "~2&    1 2 3 4 5 6 7 ")
  ;; Print the board itself
  (loop for row from 1 to 6 do
        (format t "~& ~d " "  " )
        (loop for col from 1 to 7
              for piece = (bref board (+ col (* 9 row)))
              do (format t "~c " (name-of piece))))
  ;; Finally print the time remaining for each player
  (when clock
    (format t "  [~c=~a ~c=~a]~2&"
            (name-of black) (time-string (elt clock black))
            (name-of white) (time-string (elt clock white)))))

(defun time-string (time)
  "Return a string representing this internal time in min:secs."
  (multiple-value-bind (min sec)
      (floor (round time internal-time-units-per-second) 60)
    (format nil "~2d:~2,'0d" min sec)))

;;; ********************************************

(defun println (str) (princ str) (terpri))

(terpri)
(println "**********************")
(println "   TESTING BEGINS")
(println "**********************")
(terpri)

(println "Now let's play human against minimax strategy/count-difference eval.") 
(println "Enter a move of: resign to terminate the game.")
(terpri)
(othello #'human (minimax-searcher 3 #'evaluation-fn))
(read-line)(terpri)

;; (println "Finally we play human against alpha-beta strategy/count-difference eval.") 
;; (println "Enter a move of: resign to terminate the game.")
;; (terpri)
;; (othello #'human (alpha-beta-searcher 3 #'count-difference))
;; (read-line)(terpri)

(undebug)


(terpri)
(println "**********************")
(println "   TESTING ENDED")
(println "**********************")
(terpri)

