-- Prove2me | solution 1 for D1Bound5.finiteA5_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:39:54.802777+00:00
-- url     : https://prove2.me/submissions/63b76df8-57e5-489c-8b3e-b17b52156399

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA5Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA5RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteA5_residual_norm_lt_point

section
namespace D1Bound5











private theorem finiteA5_rowfactor_scalar (X Y delta r : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hD : 0 < delta) (hXY : X ≤ Y)
    (hdelta : delta ≤ X+Y) (hr : r=delta ∨ r=X ∨ r=Y) :
    X*delta^10 ≤ 1024*Y^10*r := by
  have hdY : delta ≤ 2*Y := by linarith only [hXY,hdelta]
  have hprev : delta^9 ≤ (2*Y)^9 := by gcongr
  have hpow : delta^10 ≤ (2*Y)^10 := by gcongr
  rcases hr with rfl | rfl | rfl
  · have hh := mul_le_mul hXY hprev (by positivity) hY.le
    have hm := mul_le_mul_of_nonneg_right hh hD.le
    nlinarith only [hm,mul_nonneg (pow_nonneg hY.le 10) hD.le]
  · have hm := mul_le_mul_of_nonneg_left hpow hX.le
    nlinarith only [hm]
  · have hh := mul_le_mul hXY hpow (by positivity) hY.le
    nlinarith only [hh]

/-- The manuscript's uniform R*=495/64, derived from the actual residual. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteA5Residual x y c i‖ < (495/64 : ℝ)*‖y‖^5/(‖x‖^6*‖c‖^9) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrow := norm_pos_iff.mpr (finiteA5RowFactor_ne_zero x y hx hy hxy i)
  have hr : ‖finiteA5RowFactor x y i‖=‖x-y‖ ∨
      ‖finiteA5RowFactor x y i‖=‖x‖ ∨ ‖finiteA5RowFactor x y i‖=‖y‖ := by
    fin_cases i <;> simp [finiteA5RowFactor]
  have hh := finiteA5_rowfactor_scalar ‖x‖ ‖y‖ ‖x-y‖ ‖finiteA5RowFactor x y i‖
    hX hY hD hXY (norm_sub_le _ _) hr
  apply (finiteA5_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  have hfrac : ‖x‖*‖x-y‖^10/(‖y‖^10*‖finiteA5RowFactor x y i‖) ≤ 1024 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hh])
  have halg :
      (101/100 : ℝ)*(495/33554432)*(4^5*‖x-y‖^10/(‖x‖^5*‖y‖^5*‖c‖^9)) /
        (4*‖finiteA5RowFactor x y i‖) =
      (9999/2621440 : ℝ)*(‖x‖*‖x-y‖^10/(‖y‖^10*‖finiteA5RowFactor x y i‖))*
        (‖y‖^5/(‖x‖^6*‖c‖^9)) := by
    field_simp [hX.ne',hY.ne',hC.ne',hrow.ne']
    <;> ring
  rw [halg]
  calc
    _ ≤ (9999/2621440 : ℝ)*1024*(‖y‖^5/(‖x‖^6*‖c‖^9)) := by gcongr
    _ ≤ (495/64 : ℝ)*(‖y‖^5/(‖x‖^6*‖c‖^9)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

end D1Bound5
end
