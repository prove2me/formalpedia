-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.Mmat_preservesProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:53:05.539538+00:00
-- url     : https://prove2.me/submissions/61eb4e93-343b-4243-9f15-92e00c7a054e

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.Mmat_preservesProb
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) : PreservesProb (Mmat a b) := by

  intro v hv
  rcases hv with ⟨hv_nonneg, hvsum⟩
  have hcos_sq_a : 0 ≤ Real.cos a ^ 2 := by positivity
  have hcos_sq_b : 0 ≤ Real.cos b ^ 2 := by positivity
  have hsin_sq_a : 0 ≤ Real.sin a ^ 2 := by positivity
  have hsin_sq_b : 0 ≤ Real.sin b ^ 2 := by positivity
  have hv0 : 0 ≤ v 0 := hv_nonneg 0
  have hv1 : 0 ≤ v 1 := hv_nonneg 1
  simp only [IsProbVec, Matrix.mulVec, Mmat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.vec2_dotProduct, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Fin.forall_fin_two, Matrix.cons_dotProduct,
              Matrix.dotProduct_of_isEmpty, add_zero]
  have hsum : Real.cos a ^ 2 * v 0 + Real.cos b ^ 2 * v 1 + (Real.sin a ^ 2 * v 0 + Real.sin b ^ 2 *
      v 1) = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b, hvsum]
  refine ⟨⟨?_, ?_⟩, hsum⟩
  · nlinarith
  · nlinarith
