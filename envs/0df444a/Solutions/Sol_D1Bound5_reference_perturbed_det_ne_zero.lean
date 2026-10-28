-- Prove2me | solution 1 for D1Bound5.reference_perturbed_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:43:53.080908+00:00
-- url     : https://prove2.me/submissions/da3064ed-5fe0-46aa-886c-eb299cc37f54

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
import Theorems.Thm_D1Bound5_inverse_mul_halfOffDiagonal

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

/-- A small normalized correction makes the perturbed matrix nonsingular. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hc : ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1) :
    F.det ≠ 0 := by
  have hneg : ‖-(halfOffDiagonalInverse * (F - halfOffDiagonal))‖ < 1 := by
    simpa only [norm_neg] using hc
  have hunit : IsUnit (halfOffDiagonalInverse * F) := by
    rw [ref_factorization]
    simpa only [sub_neg_eq_add] using (isUnit_one_sub_of_norm_lt_one hneg)
  have hdet : (halfOffDiagonalInverse * F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  rw [Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2







end D1Bound5
end
