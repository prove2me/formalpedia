-- Prove2me | solution 1 for D1Bound5.finiteN3_residual_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:38:50.969557+00:00
-- url     : https://prove2.me/submissions/0565cf3e-878c-491f-928a-442aec3b4565

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN3Residual_Definitions
import Theorems.Thm_D1Bound5_finiteN3RowFactor_ne_zero
import Theorems.Thm_D1Bound5_finiteN3_residual_norm_lt_point

section
open Polynomial

namespace D1Bound5











private theorem finiteN3_rowfactor_scalar (X Y delta r : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hD : 0 < delta) (hXY : X ≤ Y)
    (hdelta : delta ≤ X+Y) (hr : r=delta ∨ r=X ∨ r=Y) :
    X*delta^6 ≤ 64*Y^6*r := by
  have hdY : delta ≤ 2*Y := by linarith only [hXY,hdelta]
  have h5 : delta^5 ≤ (2*Y)^5 := by gcongr
  have h6 : delta^6 ≤ (2*Y)^6 := by gcongr
  rcases hr with rfl | rfl | rfl
  · have hh := mul_le_mul hXY h5 (by positivity) hY.le
    have hm := mul_le_mul_of_nonneg_right hh hD.le
    nlinarith only [hm,mul_nonneg (pow_nonneg hY.le 6) hD.le]
  · have hm := mul_le_mul_of_nonneg_left h6 hX.le
    nlinarith only [hm]
  · have hh := mul_le_mul hXY h6 (by positivity) hY.le
    nlinarith only [hh]

/-- Uniform residual35/32, derived from the actual constructed row. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteN3Residual x y c i‖ <
      (35/32 : ℝ)*‖y‖^3/(‖x‖^4*‖c‖^6) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrow := norm_pos_iff.mpr (finiteN3RowFactor_ne_zero x y hx hy hxy i)
  have hr : ‖finiteN3RowFactor x y i‖=‖x-y‖ ∨
      ‖finiteN3RowFactor x y i‖=‖x‖ ∨ ‖finiteN3RowFactor x y i‖=‖y‖ := by
    fin_cases i <;> simp [finiteN3RowFactor]
  have hh := finiteN3_rowfactor_scalar ‖x‖ ‖y‖ ‖x-y‖
    ‖finiteN3RowFactor x y i‖ hX hY hD hXY (norm_sub_le _ _) hr
  apply (finiteN3_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  have hfrac : ‖x‖*‖x-y‖^6/(‖y‖^6*‖finiteN3RowFactor x y i‖) ≤ 64 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hh])
  have halg :
      (101/100 : ℝ)*(35/65536)*(4*‖x-y‖^2/(‖x‖*‖y‖*‖c‖^2))^3 /
        (4*‖finiteN3RowFactor x y i‖) =
      (3535/409600 : ℝ)*(‖x‖*‖x-y‖^6/(‖y‖^6*‖finiteN3RowFactor x y i‖))*
        (‖y‖^3/(‖x‖^4*‖c‖^6)) := by
    field_simp [hX.ne',hY.ne',hC.ne',hrow.ne']
    <;> ring
  rw [halg]
  calc
    _ ≤ (3535/409600 : ℝ)*64*(‖y‖^3/(‖x‖^4*‖c‖^6)) := by gcongr
    _ ≤ (35/32 : ℝ)*(‖y‖^3/(‖x‖^4*‖c‖^6)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

end D1Bound5
end
