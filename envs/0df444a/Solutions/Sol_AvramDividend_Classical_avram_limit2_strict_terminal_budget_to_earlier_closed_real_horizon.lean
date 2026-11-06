-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_strict_terminal_budget_to_earlier_closed_real_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:36:01.183455+00:00
-- url     : https://prove2.me/submissions/a256116d-e376-42df-95cc-142602613c9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Any strict-horizon terminal-inclusive original cash bound also bounds
    an earlier closed cash horizon with the identical terminal variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (S T : ℝ) (hST : S < T)
    (Terminal : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hBound : (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic S,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B := by
  calc
    _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
      apply lintegral_mono
      intro ω
      apply add_le_add_left
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
    _ ≤ B := hBound
