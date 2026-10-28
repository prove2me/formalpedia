-- Prove2me | solution 1 for D1Bound5.reference_perturbed_inverse_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:59:59.620549+00:00
-- url     : https://prove2.me/submissions/9f44b066-f6c8-4f08-a458-a233b375571e

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_inverse_mul_halfOffDiagonal
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

private theorem ref_factorization (F : Matrix (Fin 4) (Fin 4) ℂ) :
    halfOffDiagonalInverse * F =
      1 + halfOffDiagonalInverse * (F - halfOffDiagonal) := by
  calc
    halfOffDiagonalInverse * F =
        halfOffDiagonalInverse * (halfOffDiagonal + (F - halfOffDiagonal)) := by
          congr 1
          abel
    _ = halfOffDiagonalInverse * halfOffDiagonal +
        halfOffDiagonalInverse * (F - halfOffDiagonal) := mul_add _ _ _
    _ = _ := by rw [inverse_mul_halfOffDiagonal]





/-- A strict one-eighth perturbation admits a uniformly bounded inverse. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < (1/8 : ℝ)) :
    ‖F⁻¹‖ < (8/3 : ℝ) := by
  let Q := halfOffDiagonalInverse * (F - halfOffDiagonal)
  have hQ : ‖Q‖ < (1/4 : ℝ) := by
    calc
      ‖Q‖ ≤ ‖halfOffDiagonalInverse‖ * ‖F - halfOffDiagonal‖ :=
        Matrix.l2_opNorm_mul _ _
      _ = 2 * ‖F - halfOffDiagonal‖ := by rw [halfOffDiagonalInverse_norm]
      _ < 2 * (1/8 : ℝ) := mul_lt_mul_of_pos_left hnear (by norm_num)
      _ = 1/4 := by norm_num
  have hsmall : ‖Q‖ < 1 := lt_trans hQ (by norm_num)
  have hd : F.det ≠ 0 := reference_perturbed_det_ne_zero F hsmall
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hd
  have hi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hu
  have hid : halfOffDiagonalInverse = F⁻¹ + Q * F⁻¹ := by
    calc
      halfOffDiagonalInverse = (halfOffDiagonalInverse * F) * F⁻¹ := by
        rw [Matrix.mul_assoc, hi, mul_one]
      _ = (1 + Q) * F⁻¹ := by rw [ref_factorization]
      _ = F⁻¹ + Q * F⁻¹ := by rw [add_mul, one_mul]
  have hsolve : F⁻¹ = halfOffDiagonalInverse - Q * F⁻¹ := by
    rw [hid]
    abel
  have hnorm : ‖F⁻¹‖ ≤ 2 + ‖Q‖ * ‖F⁻¹‖ := by
    calc
      ‖F⁻¹‖ = ‖halfOffDiagonalInverse - Q * F⁻¹‖ := congrArg norm hsolve
      _ ≤ ‖halfOffDiagonalInverse‖ + ‖Q * F⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 + ‖Q‖ * ‖F⁻¹‖ := by
        rw [halfOffDiagonalInverse_norm]
        linarith only [Matrix.l2_opNorm_mul Q F⁻¹]
  have hinv : F⁻¹ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hi
    exact one_ne_zero hi.symm
  have hpos : 0 < ‖F⁻¹‖ := norm_pos_iff.mpr hinv
  have hstrict := mul_lt_mul_of_pos_right hQ hpos
  nlinarith only [hnorm, hstrict]



end D1Bound5
end
