-- Prove2me | solution 1 for FamousTheorems.mulVec_cramer
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.838617+00:00
-- url     : https://prove2.me/submissions/cc756e86-89d4-471b-b7ab-b44b23345d36

import Mathlib

theorem solution : ∀ {n : Type*} {α : Type*} [DecidableEq n] [Fintype n] [CommRing α]
    (A : Matrix n n α) (b : n → α), A.mulVec (A.cramer b) = A.det • b :=
  Matrix.mulVec_cramer
