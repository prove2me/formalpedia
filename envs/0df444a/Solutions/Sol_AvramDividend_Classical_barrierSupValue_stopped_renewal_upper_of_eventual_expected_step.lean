-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:41:31.612565+00:00
-- url     : https://prove2.me/submissions/54ecd691-8050-4bd8-9200-93999ebeaf40

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Mathlib.Analysis.Calculus.Deriv.Basic

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
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
      (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  let w : ℝ → ℕ → Ω → ℝ≥0∞ := fun ε n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal
        (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  have hw : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n ω, w ε n ω =
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 := Filter.Eventually.of_forall (fun ε n ω => rfl)
  have hbudget : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω) then
          ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w ε n ω) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Filter.Eventually.of_forall
    intro ω
    exact barrierSup_stopped_indicator_reward_le_killed_record_tsum
      X a q ε hq.le hε ω
  have hstep' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n,
      (∫⁻ ω, w ε (n + 1) ω ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
          (∫⁻ ω, w ε n ω ∂P) := by
    simpa only [w] using hstep
  exact barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
    X hX q hq W hW a ha hD hd w hw hbudget hstep'
