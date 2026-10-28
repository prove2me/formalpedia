-- Prove2me | solution 1 for D1Bound5.productFive_cross_div_norm_lt_11_108
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:43:48.082602+00:00
-- url     : https://prove2.me/submissions/e9b192d1-1eb1-4c92-843c-7e0396a470aa

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_productFive_bilinear_l2_le
import Theorems.Thm_D1Bound5_symmetric_inverse_bilinear_swap

section
open Matrix
open scoped NumberField

namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- Symmetry turns the cross form into one involving the controlled inverse
vector. All norms are Euclidean, while the dot product is complex bilinear. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (v w : Fin 4 → ℂ) (d : ℂ)
    (hd : d ≠ 0) (hsym : Fᵀ = F)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ <
      ‖d‖ / 9)
    (hFv : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) :
      EuclideanSpace ℂ (Fin 4))‖ < (11/12 : ℝ)) :
    ‖(v ⬝ᵥ (F⁻¹ *ᵥ w))/d‖ < (11/108 : ℝ) := by
  have hdot := productFive_bilinear_l2_le w (F⁻¹ *ᵥ v)
  have hcross : ‖w ⬝ᵥ (F⁻¹ *ᵥ v)‖ <
      (11/108 : ℝ) * ‖d‖ := by
    calc
      ‖w ⬝ᵥ (F⁻¹ *ᵥ v)‖ ≤
          ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ *
            ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) :
              EuclideanSpace ℂ (Fin 4))‖ := hdot
      _ ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ *
            (11/12 : ℝ) :=
          mul_le_mul_of_nonneg_left hFv.le (norm_nonneg _)
      _ < (‖d‖/9) * (11/12 : ℝ) :=
          mul_lt_mul_of_pos_right hw (by norm_num)
      _ = (11/108 : ℝ) * ‖d‖ := by ring
  rw [← symmetric_inverse_bilinear_swap F v w hsym, norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr hd)).mpr hcross

end D1Bound5
end
