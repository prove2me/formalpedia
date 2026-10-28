-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_two_norm_le_local
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:55:35.322989+00:00
-- url     : https://prove2.me/submissions/3984fa76-d593-4712-a78d-2a631952aee6

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_norm_le
import Theorems.Thm_D1Bound5_bennettTwoNodes_two
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_two
import Theorems.Thm_D1Bound5_bennett_delta_sum_three

section
namespace D1Bound5



/-- Actual column two of the integral Q-matrix obeys the same estimate at
the other interpolation node. -/
theorem _root_.solution
    (a b c : ℂ) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (r : ℝ) (hr : 0 < r) (hU : 0 < ‖a * b * c + a‖)
    (ha : 2 * r ≤ ‖a‖) (hab : 2 * r ≤ ‖a - b‖) :
    ‖bennettTwoClearedEntry a b c k i 2‖ ≤
      (4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2) ^ k *
        ((‖a * b * c + a‖ + r) / ‖a * b * c + a‖) *
          ((‖a * b * c + a‖ + r) /
            (r * (‖a‖ - r) * (‖a - b‖ - r))) ^ k := by
  have hrow : (if i = 2 then 1 else 0) + (if i = 0 then 1 else 0) +
      (if i = 1 then 1 else 0) = (1 : ℕ) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bennett_delta_sum_three i
  have h := bennettClearedTaylor_two_poles_norm_le a (a * b * c) a (a - b) k
    (if i = 2 then 1 else 0) (if i = 0 then 1 else 0) (if i = 1 then 1 else 0)
    hk hrow r hr hU ha hab
  unfold bennettTwoClearedEntry bennettClearedResidue
  rw [bennettTwoOtherPoles_two, bennettTwoNodes_two, norm_mul, norm_pow]
  have hscale : ‖(4 : ℂ) * a * b * (a - b) ^ 2‖ =
      4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2 := by simp [norm_mul, norm_pow]
  rw [hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
    (pow_nonneg (by positivity : 0 ≤ 4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2) k)

end D1Bound5
end
