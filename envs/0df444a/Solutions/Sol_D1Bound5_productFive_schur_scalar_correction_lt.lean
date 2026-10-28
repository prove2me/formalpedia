-- Prove2me | solution 1 for D1Bound5.productFive_schur_scalar_correction_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:57:20.899747+00:00
-- url     : https://prove2.me/submissions/c85f1155-f123-4fd3-b036-cbcad89d5c66

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

section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5





/-- Scalar bound for one entry of the rank-two Schur correction.
Only ordinary complex division and triangle inequalities are used. -/
theorem _root_.solution
    (wi wj vi vj d : ℂ)
    (hd : (54 : ℝ) ≤ ‖d‖)
    (hwi : ‖wi/d‖ < (1/18 : ℝ))
    (hwj : ‖wj/d‖ < (1/18 : ℝ))
    (hvi : ‖vi‖ < (3/4 : ℝ))
    (hvj : ‖vj‖ < (3/4 : ℝ)) :
    ‖(wi*vj + vi*wj)/d + vi*vj/d^2‖ < (9/100 : ℝ) := by
  have hdpos : (0 : ℝ) < ‖d‖ := by linarith only [hd]
  have hdn : d ≠ 0 := norm_pos_iff.mp hdpos
  have hvid : ‖vi/d‖ < (1/72 : ℝ) := by
    rw [norm_div]
    apply (div_lt_iff₀ hdpos).mpr
    linarith only [hvi, hd]
  have hvjd : ‖vj/d‖ < (1/72 : ℝ) := by
    rw [norm_div]
    apply (div_lt_iff₀ hdpos).mpr
    linarith only [hvj, hd]
  have h1 : ‖wi*vj/d‖ < (1/24 : ℝ) := by
    have heq : wi*vj/d = (wi/d)*vj := by field_simp [hdn]
    rw [heq, norm_mul]
    calc
      ‖wi/d‖ * ‖vj‖ ≤ (1/18 : ℝ)*‖vj‖ :=
        mul_le_mul_of_nonneg_right hwi.le (norm_nonneg _)
      _ < (1/18 : ℝ)*(3/4 : ℝ) :=
        mul_lt_mul_of_pos_left hvj (by norm_num)
      _ = 1/24 := by norm_num
  have h2 : ‖vi*wj/d‖ < (1/24 : ℝ) := by
    have heq : vi*wj/d = vi*(wj/d) := by field_simp [hdn]
    rw [heq, norm_mul]
    calc
      ‖vi‖ * ‖wj/d‖ ≤ (3/4 : ℝ)*‖wj/d‖ :=
        mul_le_mul_of_nonneg_right hvi.le (norm_nonneg _)
      _ < (3/4 : ℝ)*(1/18 : ℝ) :=
        mul_lt_mul_of_pos_left hwj (by norm_num)
      _ = 1/24 := by norm_num
  have h3 : ‖vi*vj/d^2‖ < (1/5184 : ℝ) := by
    have heq : vi*vj/d^2 = (vi/d)*(vj/d) := by field_simp [hdn]
    rw [heq, norm_mul]
    calc
      ‖vi/d‖*‖vj/d‖ ≤ (1/72 : ℝ)*‖vj/d‖ :=
        mul_le_mul_of_nonneg_right hvid.le (norm_nonneg _)
      _ < (1/72 : ℝ)*(1/72 : ℝ) :=
        mul_lt_mul_of_pos_left hvjd (by norm_num)
      _ = 1/5184 := by norm_num
  have hpair : ‖(wi*vj + vi*wj)/d‖ < (1/12 : ℝ) := by
    rw [add_div]
    have hh := norm_add_le (wi*vj/d) (vi*wj/d)
    linarith only [hh,h1,h2]
  have hh := norm_add_le ((wi*vj+vi*wj)/d) (vi*vj/d^2)
  have hnum : (1/12 : ℝ) + 1/5184 < 9/100 := by norm_num
  linarith only [hh,hpair,h3,hnum]





end D1Bound5
end
