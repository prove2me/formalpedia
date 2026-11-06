-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:22:55.602418+00:00
-- url     : https://prove2.me/submissions/e6850d21-7faa-47f8-b7ce-cad7a732fa26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  exact paymentTimes_min_ofReal_subset_inter_horizon (ruinTime X x D ω) T hT
