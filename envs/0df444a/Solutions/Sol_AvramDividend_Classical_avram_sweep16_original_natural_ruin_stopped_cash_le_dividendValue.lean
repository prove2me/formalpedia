-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_natural_ruin_stopped_cash_le_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:02:54.923909+00:00
-- url     : https://prove2.me/submissions/fba984b0-1fbd-4180-8436-100320d52ab6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by
  have hclosed :=
    avram_sweep16_original_closed_window_cash_le_dividendValue X q x (n : ℝ) D
  apply le_trans ?_ hclosed
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  have hcast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by
    simp
  simpa only [hcast] using
    (paymentTimes_min_ofReal_subset_inter_horizon
      (ruinTime X x D ω) (n : ℝ) (by positivity))
