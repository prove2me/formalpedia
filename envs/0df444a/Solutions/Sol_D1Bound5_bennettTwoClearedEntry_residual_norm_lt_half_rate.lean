-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_residual_norm_lt_half_rate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:23:04.180563+00:00
-- url     : https://prove2.me/submissions/e688218f-6ab4-4cbc-a3b8-e7ea3e2b9b78

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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_residual_norm_le
import Theorems.Thm_D1Bound5_bennettTwoResidualGammaBound_lt_half_rate

section
namespace D1Bound5











/-- Final residual inequality for every actual row of the integral Q-matrix,
with exactly the manuscript's rate R2 and factor one half. -/
theorem _root_.solution
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1 < ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)‖ <
      1 / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) := by
  exact (bennettTwoClearedEntry_residual_norm_le a b c ha hb hc hab hAB hAC k hk i).trans_lt
    (bennettTwoResidualGammaBound_lt_half_rate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖
      (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hc)
      (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) hAC k hk)

end D1Bound5
end
