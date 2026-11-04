-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_ae_finite_of_summable_nu_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:03:51.720737+00:00
-- url     : https://prove2.me/submissions/0e515db9-0beb-47ca-99bf-c89a78921780

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_simple_integral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A true source-original intrinsic predictable simple jump integral is
finite almost surely under a summable rate budget and original rate facts. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) = (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hFinite : (∑' i, (∫⁻ ω, H i ω ∂P) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) ≠ ∞) :
    ∀ᵐ ω ∂P, (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) < ∞ := by
  exact MeasureTheory.ae_lt_top
    (avram_p2_f_weighted_original_countable_simple_integral_measurable
      X s T B hB H hH)
    (by
      rw [avram_p2_f_weighted_original_countable_intrinsic_integral_conditional_nu_rates
        X s T B hB H hH hOrigin]
      exact hFinite)
