-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger85_original_strict_interior_cash_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:47:53.815397+00:00
-- url     : https://prove2.me/submissions/44f2ecdc-55ca-42e1-b111-0b22f40653c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (ρ a b : ℝ≥0) (hb : b < ρ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) := by
  have hbR : (b : ℝ) < (ρ : ℝ) := by exact_mod_cast hb
  apply lintegral_mono_set
  intro s hs
  exact ⟨hs.1, lt_of_le_of_lt hs.2.2 hbR⟩
