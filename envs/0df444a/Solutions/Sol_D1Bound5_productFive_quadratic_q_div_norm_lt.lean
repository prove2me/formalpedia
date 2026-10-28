-- Prove2me | solution 1 for D1Bound5.productFive_quadratic_q_div_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:41:51.408264+00:00
-- url     : https://prove2.me/submissions/288c2bca-eaa8-4f43-ac3a-95a64a9ab972

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_productFive_bilinear_l2_le
import Theorems.Thm_D1Bound5_reference_perturbed_inverse_norm_lt

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- The quadratic bilinear form involving the first-four-entry vector is
small relative to the square of the last entry. Neither the matrix nor its
inverse is assumed Hermitian. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (d : ℂ)
    (hd : d ≠ 0)
    (hnear : ‖F - halfOffDiagonal‖ < (1/8 : ℝ))
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ < ‖d‖ / 9) :
    ‖(w ⬝ᵥ (F⁻¹ *ᵥ w))/d^2‖ < (8/243 : ℝ) := by
  let x : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 w
  have hn : 0 ≤ ‖x‖ := norm_nonneg _
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hInv : ‖F⁻¹‖ < (8/3 : ℝ) :=
    reference_perturbed_inverse_norm_lt F hnear
  have hv : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ w) :
      EuclideanSpace ℂ (Fin 4))‖ ≤ ‖F⁻¹‖ * ‖x‖ := by
    exact Matrix.l2_opNorm_mulVec F⁻¹ x
  have hq : ‖w ⬝ᵥ (F⁻¹ *ᵥ w)‖ ≤ ‖F⁻¹‖ * ‖x‖^2 := by
    calc
      _ ≤ ‖x‖ * ‖(WithLp.toLp 2 (F⁻¹ *ᵥ w) :
              EuclideanSpace ℂ (Fin 4))‖ :=
        productFive_bilinear_l2_le w (F⁻¹ *ᵥ w)
      _ ≤ ‖x‖ * (‖F⁻¹‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left hv hn
      _ = ‖F⁻¹‖ * ‖x‖^2 := by ring
  have hsq : ‖x‖^2 < (‖d‖/9)^2 := by
    have hp := mul_pos (sub_pos.mpr hw)
      (by linarith only [hw, hn, hdpos] : 0 < ‖d‖/9 + ‖x‖)
    nlinarith only [hp]
  have hbound : ‖w ⬝ᵥ (F⁻¹ *ᵥ w)‖ < ‖d‖^2 * (8/243 : ℝ) := by
    calc
      _ ≤ ‖F⁻¹‖ * ‖x‖^2 := hq
      _ ≤ (8/3 : ℝ) * ‖x‖^2 :=
        mul_le_mul_of_nonneg_right hInv.le (sq_nonneg _)
      _ < (8/3 : ℝ) * (‖d‖/9)^2 :=
        mul_lt_mul_of_pos_left hsq (by norm_num)
      _ = ‖d‖^2 * (8/243 : ℝ) := by ring
  rw [norm_div, norm_pow]
  apply (div_lt_iff₀ (pow_pos hdpos 2)).mpr
  simpa [mul_comm] using hbound



end D1Bound5
end
