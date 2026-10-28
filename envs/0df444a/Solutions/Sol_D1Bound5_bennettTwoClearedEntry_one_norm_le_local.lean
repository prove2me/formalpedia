-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_one_norm_le_local
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:46.118209+00:00
-- url     : https://prove2.me/submissions/de659e1a-d081-425b-a05b-93709751223c

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
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_one
import Theorems.Thm_D1Bound5_bennett_delta_sum_three

section
namespace D1Bound5

/-- Actual column one of the integral Q-matrix obeys the local positive-series
bound, with its directed pole displacements and exact clearing factor. -/
theorem _root_.solution
    (a b c : ℂ) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (r : ℝ) (hr : 0 < r) (hU : 0 < ‖a * b * c + b‖)
    (hb : 2 * r ≤ ‖b‖) (hab : 2 * r ≤ ‖a - b‖) :
    ‖bennettTwoClearedEntry a b c k i 1‖ ≤
      (4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2) ^ k *
        ((‖a * b * c + b‖ + r) / ‖a * b * c + b‖) *
          ((‖a * b * c + b‖ + r) /
            (r * (‖b‖ - r) * (‖a - b‖ - r))) ^ k := by
  have hrow : (if i = 1 then 1 else 0) + (if i = 0 then 1 else 0) +
      (if i = 2 then 1 else 0) = (1 : ℕ) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bennett_delta_sum_three i
  have h := bennettClearedTaylor_two_poles_norm_le b (a * b * c) b (b - a) k
    (if i = 1 then 1 else 0) (if i = 0 then 1 else 0) (if i = 2 then 1 else 0)
    hk hrow r hr hU hb (by simpa only [norm_sub_rev] using hab)
  rw [norm_sub_rev] at h
  unfold bennettTwoClearedEntry bennettClearedResidue
  rw [bennettTwoOtherPoles_one, bennettTwoNodes_one, norm_mul, norm_pow]
  have hscale : ‖(4 : ℂ) * a * b * (a - b) ^ 2‖ =
      4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2 := by simp [norm_mul, norm_pow]
  rw [hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
    (pow_nonneg (by positivity : 0 ≤ 4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2) k)



end D1Bound5
end
