-- Prove2me | solution 1 for D1Bound5.adjugate_eq_det_smul_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:30.93399+00:00
-- url     : https://prove2.me/submissions/6c8cf0e0-7c65-4685-bd3c-c5b0dc8ed006

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

section
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace
open Matrix

namespace D1Bound5





/-- Express the adjugate of an invertible matrix in terms of its inverse. -/
theorem _root_.solution (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : F.det ≠ 0) : F.adjugate = F.det • F⁻¹ := by
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hd
  calc
    F.adjugate = (F⁻¹ * F) * F.adjugate := by
      rw [Matrix.nonsing_inv_mul F hu, one_mul]
    _ = F⁻¹ * (F * F.adjugate) := Matrix.mul_assoc _ _ _
    _ = F⁻¹ * (F.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
      rw [Matrix.mul_adjugate]
    _ = F.det • F⁻¹ := by simp





end D1Bound5
end
