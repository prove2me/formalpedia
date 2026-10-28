-- Prove2me | solution 1 for D1Bound5.finiteN3_residual_norm_lt_max
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:30.638925+00:00
-- url     : https://prove2.me/submissions/f98dd28f-e86c-4ade-8d63-35d294e1ad5e

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
namespace D1Bound5

/-- The exact row factors yield the distance-sensitive maximum before
any independent bounds on anchor distances are taken. -/
theorem _root_.solution (x y c : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y)
    (hXY : ‖x‖ ≤ ‖y‖) (hXC : 1000 ≤ ‖x‖*‖c‖) (i : Fin 3) :
    ‖finiteN3Residual x y c i‖ <
      (3535/409600 : ℝ)*max (‖x-y‖^6) (‖x‖*‖x-y‖^5)/
        (‖x‖^4*‖y‖^3*‖c‖^6) := by
  have hX := norm_pos_iff.mpr hx
  have hY := norm_pos_iff.mpr hy
  have hC := norm_pos_iff.mpr hc
  have hD := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrow := norm_pos_iff.mpr (finiteN3RowFactor_ne_zero x y hx hy hxy i)
  let M := max (‖x-y‖^6) (‖x‖*‖x-y‖^5)
  have hM0 : ‖x-y‖^6 ≤ M := le_max_left _ _
  have hM1 : ‖x‖*‖x-y‖^5 ≤ M := le_max_right _ _
  have hscalar : ‖x‖*‖x-y‖^6 ≤ M*‖finiteN3RowFactor x y i‖ := by
    fin_cases i
    · have hh := mul_le_mul_of_nonneg_right hM1 hD.le
      simpa [finiteN3RowFactor,pow_succ,mul_assoc] using hh
    · have hh := mul_le_mul_of_nonneg_left hM0 hX.le
      simpa [finiteN3RowFactor,mul_comm] using hh
    · have hh := mul_le_mul_of_nonneg_left hM0 hY.le
      have hh' := mul_le_mul_of_nonneg_right hXY (pow_nonneg hD.le 6)
      simpa [finiteN3RowFactor,mul_comm] using hh'.trans hh
  have hf : ‖x‖*‖x-y‖^6/‖finiteN3RowFactor x y i‖ ≤ M :=
    (div_le_iff₀ hrow).mpr hscalar
  apply (finiteN3_residual_norm_lt_point x y c hx hy hc hxy hXY hXC i).trans_le
  calc
    _ = (3535/409600 : ℝ)*(‖x‖*‖x-y‖^6/‖finiteN3RowFactor x y i‖)/
        (‖x‖^4*‖y‖^3*‖c‖^6) := by
      field_simp [hX.ne',hY.ne',hC.ne',hrow.ne']
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hf (by norm_num)) (by positivity)



end D1Bound5
end
