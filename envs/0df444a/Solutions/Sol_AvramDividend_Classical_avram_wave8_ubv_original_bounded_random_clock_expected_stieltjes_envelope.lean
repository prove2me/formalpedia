-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:46:57.679211+00:00
-- url     : https://prove2.me/submissions/fd72a2af-d499-416a-9463-3c8be895693d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Any bounded random original payout clock inherits the finite exact
    complete Stieltjes expectation envelope of its deterministic bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp
      (|X.ψ 1 - q| * (((((T : ℝ).toNNReal + 1 : ℝ≥0) : ℝ))))) *
    ENNReal.ofReal (Real.exp x) := by
  have hfull :=
    avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
      X x C D hD (T : ℝ) (NNReal.coe_nonneg T) q
  calc
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) := by
        apply lintegral_mono
        intro ω
        apply lintegral_mono_set
        intro s hs
        have hboundReal : (τ ω : ℝ) ≤ (T : ℝ) := by
          exact_mod_cast hτBound ω
        exact ⟨hs.1, le_trans hs.2 hboundReal⟩
    _ ≤ _ := hfull
end
