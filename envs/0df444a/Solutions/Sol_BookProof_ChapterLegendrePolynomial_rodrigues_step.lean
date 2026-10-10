-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.rodrigues_step
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:29:07.759372+00:00
-- url     : https://prove2.me/submissions/8765a013-98ff-47c9-b8f6-8f9c442df898

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.rodrigues_step
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) :
    (X ^ 2 - 1) * derivative ((X ^ 2 - 1) ^ l) = C (2 * (l : ℝ)) * X * (X ^ 2 - 1) ^ l := by

  rcases l with _ | l
  · simp
  · rw [derivative_pow]
    simp only [derivative_sub, derivative_X_pow, derivative_one, Nat.add_sub_cancel]
    push_cast
    simp only [C_add, C_1, C_mul, map_ofNat]
    ring_nf
