-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger84_original_strict_final_cell_cash_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:28:53.2149+00:00
-- url     : https://prove2.me/submissions/71e0df8a-4738-4270-9d9d-92ef0215e95f

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
    (q : ℝ) (ρ δ a : ℝ≥0)
    (ha : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hab : a ≤ ρ) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) := by
  apply lintegral_mono_set
  intro s hs
  rcases hs with ⟨hpay, hioo⟩
  exact ⟨hpay, ⟨lt_of_le_of_lt ha hioo.1, hioo.2⟩⟩
