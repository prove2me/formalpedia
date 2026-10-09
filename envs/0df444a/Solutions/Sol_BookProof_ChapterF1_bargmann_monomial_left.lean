-- Prove2me | solution 1 for BookProof.ChapterF1.bargmann_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:55:38.727102+00:00
-- url     : https://prove2.me/submissions/89ec562b-b972-4720-9831-f56cbd9bb6f0

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.bargmann_monomial_left
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (q : ℂ[X]) :
    bargmann (X ^ m) q = (m.factorial : ℂ) * q.coeff m := by

  unfold bargmann;
  rw [ Finset.sum_eq_single m ] <;> simp_all [ Polynomial.coeff_X_pow ]
