-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_weighted_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:39.457342+00:00
-- url     : https://prove2.me/submissions/adb956dd-9089-4d6c-b30e-af665a893902

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedEntry_height_bounds
import Theorems.Thm_D1Bound5_bennett_weighted_even_power_le

section
namespace D1Bound5



/-- The actual two anchor columns satisfy the combined height bound used
in the integral approximation form, with no coefficient bound premise. -/
theorem _root_.solution
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoClearedEntry a b c k i 1‖/‖a‖ +
        ‖bennettTwoClearedEntry a b c k i 2‖/‖b‖ <
      2*(42*‖b‖^3*‖c‖)^k/‖b‖ := by
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  obtain ⟨h1, h2⟩ := bennettTwoClearedEntry_height_bounds
    a b c ha hb hc hab hAB hAC k hk i
  have hpower : (42*‖a‖^2*‖b‖*‖c‖)^k/‖a‖ ≤
      (42*‖b‖^3*‖c‖)^k/‖b‖ := by
    have heqA : 42*‖a‖^2*‖b‖*‖c‖ = ‖a‖^2*(42*‖b‖*‖c‖) := by ring
    have heqB : 42*‖b‖^3*‖c‖ = ‖b‖^2*(42*‖b‖*‖c‖) := by ring
    rw [heqA, heqB]
    exact bennett_weighted_even_power_le ‖a‖ ‖b‖ (42*‖b‖*‖c‖)
      hA hB hAB (by positivity) k hk
  have hfirst := (div_lt_div_of_pos_right h1 hA).trans_le hpower
  have hsecond := div_lt_div_of_pos_right h2 hB
  calc
    _ < (42*‖b‖^3*‖c‖)^k/‖b‖ + (42*‖b‖^3*‖c‖)^k/‖b‖ :=
      add_lt_add hfirst hsecond
    _ = _ := by ring

end D1Bound5
end
