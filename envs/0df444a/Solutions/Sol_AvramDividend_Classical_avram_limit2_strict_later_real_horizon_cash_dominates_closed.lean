-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_strict_later_real_horizon_cash_dominates_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:35:55.614477+00:00
-- url     : https://prove2.me/submissions/99ec5026-9bbc-4ad0-9424-54b15583a130

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Original closed cash through S is covered by strict cash before T
    whenever S < T, preserving every payment made exactly at S. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (S T : ℝ) (hST : S < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic S,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  intro t ht
  exact ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
