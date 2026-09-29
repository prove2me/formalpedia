-- Prove2me | solution 1 for FamousTheorems.aeval_self_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:48.067331+00:00
-- url     : https://prove2.me/submissions/0ebe0640-1b03-4381-bcdf-2c59c4dd92c7

import Mathlib

theorem solution : ∀ {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n R), (Polynomial.aeval M) M.charpoly = 0 :=
  Matrix.aeval_self_charpoly
