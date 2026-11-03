-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:58:27.322922+00:00
-- url     : https://prove2.me/submissions/b9c40df9-0cf2-459f-9562-614ca0816992

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform natural ruin-clock budgets bound the original-process full-ruin
    finite-horizon Stieltjes expectation, without an extra measurability axiom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (B : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by
  apply avram_wave7_11_ruin_clock_outer_lintegral_bound_of_measurable_trunc
    D (fun ω => ruinTime X x D ω) q T B ?_ hBound
  intro n
  exact avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
    X x D hD q T (fun _ : Ω => (n : ℝ≥0∞)) measurable_const
