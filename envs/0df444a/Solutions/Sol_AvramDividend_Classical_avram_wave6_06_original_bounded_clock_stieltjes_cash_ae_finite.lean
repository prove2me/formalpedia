-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:08:54.418695+00:00
-- url     : https://prove2.me/submissions/979f8de4-6358-44a6-8c37-1748feb447f6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual source dividend reward at a bounded random clock inherits the
a.e. finiteness of its complete deterministic-horizon Stieltjes envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by
  have hT : (0 : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le)
  have hFull :=
    avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
      X x C D hD (T : ℝ) hT q
  filter_upwards [hFull] with ω hFinite
  have hBound : (τ ω : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hτBound ω
  have hSubset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) := by
    rintro s ⟨hsPay, hsTime⟩
    exact ⟨hsPay, le_trans hsTime hBound⟩
  exact lt_of_le_of_lt (lintegral_mono_set hSubset) hFinite
