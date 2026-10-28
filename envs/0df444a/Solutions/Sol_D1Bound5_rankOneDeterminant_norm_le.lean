-- Prove2me | solution 1 for D1Bound5.rankOneDeterminant_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:04.156934+00:00
-- url     : https://prove2.me/submissions/b17cd2d9-43ab-43a2-a879-66d5fe900789

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bilinear_mulVec_norm_le
import Theorems.Thm_D1Bound5_rankOneDeterminant

section
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace
open Matrix

namespace D1Bound5







/-- Determinant bound for a rank-one update, using the inverse norm. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    ‖(F + Matrix.vecMulVec w w).det‖ ≤
      ‖F.det‖ * (1 + ‖F⁻¹‖ * (∑ i, ‖w i‖ ^ 2)) := by
  have htriangle :
      ‖(1 : ℂ) + w ⬝ᵥ (F⁻¹ *ᵥ w)‖ ≤
        1 + ‖w ⬝ᵥ (F⁻¹ *ᵥ w)‖ := by
    simpa only [norm_one] using
      norm_add_le (1 : ℂ) (w ⬝ᵥ (F⁻¹ *ᵥ w))
  have hquad := bilinear_mulVec_norm_le F⁻¹ w
  calc
    ‖(F + Matrix.vecMulVec w w).det‖ =
        ‖F.det‖ * ‖(1 : ℂ) + w ⬝ᵥ (F⁻¹ *ᵥ w)‖ := by
          rw [rankOneDeterminant F w hF, norm_mul]
    _ ≤ ‖F.det‖ * (1 + ‖w ⬝ᵥ (F⁻¹ *ᵥ w)‖) :=
      mul_le_mul_of_nonneg_left htriangle (norm_nonneg _)
    _ ≤ ‖F.det‖ * (1 + ‖F⁻¹‖ * (∑ i, ‖w i‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith only [hquad]



end D1Bound5
end
