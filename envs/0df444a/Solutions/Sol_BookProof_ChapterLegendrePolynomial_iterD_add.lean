-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.iterD_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:27:59.365631+00:00
-- url     : https://prove2.me/submissions/900610eb-b555-4f01-9ab8-a199932202b4

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.iterD_add
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (p q : ℝ[X]) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by

  induction k generalizing p q with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        derivative_add, ih]
