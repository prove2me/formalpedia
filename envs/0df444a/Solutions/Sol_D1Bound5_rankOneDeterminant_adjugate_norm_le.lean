-- Prove2me | solution 1 for D1Bound5.rankOneDeterminant_adjugate_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:35.386979+00:00
-- url     : https://prove2.me/submissions/dad10ec0-773c-4191-9307-db9fe19ecd6c

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
import Theorems.Thm_D1Bound5_adjugate_eq_det_smul_inverse
import Theorems.Thm_D1Bound5_rankOneDeterminant_norm_le

section
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace
open Matrix

namespace D1Bound5









/-- The rank-one determinant bound in precisely the cofactor form required
by the determinant argument in lem:product-four. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    ‖(F + Matrix.vecMulVec w w).det‖ ≤
      ‖F.det‖ + ‖F.adjugate‖ * (∑ i, ‖w i‖ ^ 2) := by
  have hadj : ‖F.adjugate‖ = ‖F.det‖ * ‖F⁻¹‖ := by
    rw [adjugate_eq_det_smul_inverse F hF, norm_smul]
  calc
    ‖(F + Matrix.vecMulVec w w).det‖
        ≤ ‖F.det‖ * (1 + ‖F⁻¹‖ * (∑ i, ‖w i‖ ^ 2)) :=
          rankOneDeterminant_norm_le F w hF
    _ = ‖F.det‖ + ‖F.adjugate‖ * (∑ i, ‖w i‖ ^ 2) := by
      rw [hadj]
      ring

end D1Bound5
end
