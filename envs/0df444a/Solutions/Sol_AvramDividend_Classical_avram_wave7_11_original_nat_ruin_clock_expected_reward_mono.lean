-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_nat_ruin_clock_expected_reward_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:48.879435+00:00
-- url     : https://prove2.me/submissions/011ec6df-c56e-4815-8a8a-b078c37ed41e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expected discounted original Stieltjes payments increase with the
    natural-number truncation of the genuine ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (n m : ℕ) (hnm : n ≤ m) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  have hcast : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hnm
  exact ⟨paymentTimes_min_mono_horizon
    (ruinTime X x D ω) _ _ hcast ht.1, ht.2⟩
