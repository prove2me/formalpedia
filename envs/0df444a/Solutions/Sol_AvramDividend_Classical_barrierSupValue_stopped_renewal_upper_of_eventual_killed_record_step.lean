-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:44:52.064228+00:00
-- url     : https://prove2.me/submissions/d539af4a-add5-4749-ab66-96d8cd667713

import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (w : ℝ → ℕ → Ω → ℝ≥0∞)
    (hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n ω, w ε n ω =
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0)
    (hbudget : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w ε n ω))
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n,
      (∫⁻ ω, w ε (n + 1) ω ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
          (∫⁻ ω, w ε n ω ∂P)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hinc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) :=
    monotone_nonzero_derivative_eventually_right_increment W a hmono hD hd
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  filter_upwards [hinc, hε, hw, hbudget, hstep] with ε hincε hεpos hwε hbudgetε hstepε
  exact barrierSupValue_le_right_scale_quotient_of_killed_grid_step
    X W a 0 q ε (le_of_lt hq) hεpos
    (lt_trans hWa hincε) (le_of_lt hWa) hincε
    (w ε) (by simpa only [zero_add] using hwε)
    hbudgetε hstepε
