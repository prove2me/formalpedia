-- Prove2me | solution 1 for D1Bound5.productFive_selfBilinear_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:59:34.400917+00:00
-- url     : https://prove2.me/submissions/ab94ff57-1839-47db-adf5-b2bc751a4794

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





end D1Bound5

open scoped InnerProductSpace

namespace D1Bound5



/-- The bilinear p-form is bounded by one under the quantitative last-column
and inverse-vector estimates. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ <
      (201/200 : ℝ))
    (hFv : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin 4))‖ <
      (11/12 : ℝ)) :
    ‖v ⬝ᵥ (F⁻¹ *ᵥ v)‖ < 1 := by
  calc
    ‖v ⬝ᵥ (F⁻¹ *ᵥ v)‖ ≤
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ *
          ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin 4))‖ :=
      productFive_bilinear_l2_le v (F⁻¹ *ᵥ v)
    _ ≤ (201/200 : ℝ) *
          ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin 4))‖ :=
      mul_le_mul_of_nonneg_right hv.le (norm_nonneg _)
    _ < (201/200 : ℝ) * (11/12 : ℝ) :=
      mul_lt_mul_of_pos_left hFv (by norm_num)
    _ < 1 := by norm_num



end D1Bound5
end
