-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_zero_stop_contact_tail_cash_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:12:35.955222+00:00
-- url     : https://prove2.me/submissions/90701f22-7427-4b48-9473-702711916aa8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A zero stopped clock has no strictly positive tail cell; initial D-payment remains separate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (T : ℝ≥0)
    (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    τ = 0 →
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  change τ = 0 → _
  intro hτ
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0
  have hCell : Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ) = ∅ := by
    simp [hτ]
  rw [hCell]
  simp
