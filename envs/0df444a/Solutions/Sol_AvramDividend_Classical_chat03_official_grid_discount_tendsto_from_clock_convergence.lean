-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_grid_discount_tendsto_from_clock_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:27:11.36691+00:00
-- url     : https://prove2.me/submissions/d78fb040-31f5-4fc7-a6de-159482baf4a7

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The official named upper/lower clocks automatically satisfy the
finite-tie exclusion needed for discounted grid convergence.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop
      (𝓝 (twoSidedExitUpTime X upper ω)))
    (hd : Tendsto downGrid atTop
      (𝓝 (twoSidedExitDownTime X lower ω)))
    (hNoUpGrid : twoSidedExitUpTime X upper ω = ∞ →
      ∀ n : ℕ, upGrid n = ∞) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by
  have hfiniteTie :
      twoSidedExitUpTime X upper ω =
        twoSidedExitDownTime X lower ω →
      twoSidedExitUpTime X upper ω = ∞ := by
    intro heq
    by_contra hfinite
    have hup :
        twoSidedExitUpTime X upper ω =
          ((twoSidedExitUpTime X upper ω).toNNReal : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal hfinite).symm
    have hdown :
        twoSidedExitDownTime X lower ω =
          ((twoSidedExitUpTime X upper ω).toNNReal : ℝ≥0∞) := by
      rw [← heq]
      exact hup
    exact chat03_official_strict_passage_no_finite_ties
      X ω lower upper hsep
      (twoSidedExitUpTime X upper ω).toNNReal
      hup hdown
  exact chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
    q (twoSidedExitUpTime X upper ω)
      (twoSidedExitDownTime X lower ω)
    upGrid downGrid hu hd hfiniteTie hNoUpGrid
