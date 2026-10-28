-- Prove2me | solution 1 for D1Bound5.finiteA4_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:41.758474+00:00
-- url     : https://prove2.me/submissions/74c85d59-3968-4140-bbf3-008aaabb841d

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteA4Residual_Definitions
import Theorems.Thm_D1Bound5_finiteA4RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteA4_residual_norm_lt_point

section
namespace D1Bound5











private theorem finiteA4_rowfactor_scalar (X Y delta r : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hD : 0 < delta) (hXY : X ≤ Y)
    (hdelta : delta ≤ X+Y) (hr : r=delta ∨ r=X ∨ r=Y) :
    X*delta^8 ≤ 256*Y^8*r := by
  have hdY : delta ≤ 2*Y := by linarith only [hXY,hdelta]
  have hprev : delta^7 ≤ (2*Y)^7 := by gcongr
  have hpow : delta^8 ≤ (2*Y)^8 := by gcongr
  rcases hr with rfl | rfl | rfl
  · have hh := mul_le_mul hXY hprev (by positivity) hY.le
    have hm := mul_le_mul_of_nonneg_right hh hD.le
    nlinarith only [hm,mul_nonneg (pow_nonneg hY.le 8) hD.le]
  · have hm := mul_le_mul_of_nonneg_left hpow hX.le
    nlinarith only [hm]
  · have hh := mul_le_mul hXY hpow (by positivity) hY.le
    nlinarith only [hh]

/-- The manuscript's uniform R*=63/8, derived from the actual residual. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteA4Residual x y c i‖ < (63/8 : ℝ)*‖y‖^4/(‖x‖^5*‖c‖^7) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrow := norm_pos_iff.mpr (finiteA4RowFactor_ne_zero x y hx hy hxy i)
  have hr : ‖finiteA4RowFactor x y i‖=‖x-y‖ ∨
      ‖finiteA4RowFactor x y i‖=‖x‖ ∨ ‖finiteA4RowFactor x y i‖=‖y‖ := by
    fin_cases i <;> simp [finiteA4RowFactor]
  have hh := finiteA4_rowfactor_scalar ‖x‖ ‖y‖ ‖x-y‖ ‖finiteA4RowFactor x y i‖
    hX hY hD hXY (norm_sub_le _ _) hr
  apply (finiteA4_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  have hfrac : ‖x‖*‖x-y‖^8/(‖y‖^8*‖finiteA4RowFactor x y i‖) ≤ 256 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hh])
  have halg :
      (101/100 : ℝ)*(63/524288)*(4^4*‖x-y‖^8/(‖x‖^4*‖y‖^4*‖c‖^7)) /
        (2*‖finiteA4RowFactor x y i‖) =
      (6363/409600 : ℝ)*(‖x‖*‖x-y‖^8/(‖y‖^8*‖finiteA4RowFactor x y i‖))*
        (‖y‖^4/(‖x‖^5*‖c‖^7)) := by
    field_simp [hX.ne',hY.ne',hC.ne',hrow.ne']
    <;> ring
  rw [halg]
  calc
    _ ≤ (6363/409600 : ℝ)*256*(‖y‖^4/(‖x‖^5*‖c‖^7)) := by gcongr
    _ ≤ (63/8 : ℝ)*(‖y‖^4/(‖x‖^5*‖c‖^7)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

end D1Bound5
end
