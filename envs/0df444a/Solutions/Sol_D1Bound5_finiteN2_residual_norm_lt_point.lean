-- Prove2me | solution 1 for D1Bound5.finiteN2_residual_norm_lt_point
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:36.220455+00:00
-- url     : https://prove2.me/submissions/4ae351ac-2192-4dc3-8c89-b89b5d6d47fe

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
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions
import Theorems.Thm_D1Bound5_finiteN2_bennett_residual_norm_lt
import Theorems.Thm_D1Bound5_finiteN2_residual_identity

section
namespace D1Bound5











/-- The actual finite N2 point residual, preserving the distance factor
needed by the fixed-anchor interval tables. This is exactly the paper's
max(delta^4,u*delta^3) normalization, with denominators multiplied out. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteN2Residual x y c i‖ <
      (101/2560 : ℝ)*max (‖x-y‖^4) (‖x‖*‖x-y‖^3) /
        (‖x‖^3*‖y‖^2*‖c‖^4) := by
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hC : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hδ : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let u : Fin 3 → ℝ := ![‖x‖*‖x-y‖^3,‖x-y‖^4,(‖x‖/‖y‖)*‖x-y‖^4]
  have hf : 0 < 2*‖finiteN2RowFactor x y i‖ := by
    fin_cases i
    · simpa [finiteN2RowFactor] using mul_pos (show (0 : ℝ) < 2 by norm_num) hδ
    · simpa [finiteN2RowFactor] using mul_pos (show (0 : ℝ) < 2 by norm_num) hX
    · simpa [finiteN2RowFactor] using mul_pos (show (0 : ℝ) < 2 by norm_num) hY
  have h := finiteN2_bennett_residual_norm_lt x y c hx hy hc hxy hXY hXC i
  rw [finiteN2_residual_identity x y c hx hy hc hxy, norm_mul, norm_mul] at h
  norm_num at h
  have hdiv : ‖finiteN2Residual x y c i‖ <
      ((101/1280 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4)) /
        (2*‖finiteN2RowFactor x y i‖) := by
    apply (lt_div_iff₀ hf).mpr
    nlinarith only [h]
  have hscale : ((101/1280 : ℝ)*‖x-y‖^4/(‖x‖^2*‖y‖^2*‖c‖^4)) /
        (2*‖finiteN2RowFactor x y i‖) =
      (101/2560 : ℝ)*u i/(‖x‖^3*‖y‖^2*‖c‖^4) := by
    fin_cases i <;> simp [finiteN2RowFactor,u]
    all_goals field_simp [hX.ne',hY.ne',hC.ne',hδ.ne']
    all_goals ring
  have hu : u i ≤ max (‖x-y‖^4) (‖x‖*‖x-y‖^3) := by
    fin_cases i
    · exact le_max_right _ _
    · exact le_max_left _ _
    · calc
        _ ≤ 1*‖x-y‖^4 := mul_le_mul_of_nonneg_right
          ((div_le_one hY).mpr hXY) (pow_nonneg (norm_nonneg _) _)
        _ ≤ _ := by simpa only [one_mul] using le_max_left (‖x-y‖^4) (‖x‖*‖x-y‖^3)
  rw [hscale] at hdiv
  exact hdiv.trans_le (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hu (by norm_num)) (by positivity))



end D1Bound5
end
