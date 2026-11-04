-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_st_conditional_nu_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:59:13.24371+00:00
-- url     : https://prove2.me/submissions/65d26bf2-a68e-4e71-84ed-41e28f696256

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- True original countable marked jump-measure compensation on
ordered time cells, conditional on independent zero-origin ν rates. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (t i - s i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  have hEndpoint (i : ι) : s i + (t i - s i) = t i := by
    calc
      s i + (t i - s i) = (t i - s i) + s i := add_comm _ _
      _ = t i := tsub_add_cancel_of_le (hst i)
  simpa only [hEndpoint] using
    (avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates
      X s (fun i => t i - s i) B hB H hH hOrigin)
