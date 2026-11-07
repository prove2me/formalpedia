-- Prove2me | solution 17 for AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:22:11.633046+00:00
-- url     : https://prove2.me/submissions/26ebba67-50aa-4f0f-8c74-2e0f1a035810
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_signed_fatou_grids_to_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_aggregate_L1_signed_strict_to_closed_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original BV complement via the physical Fatou family and zero-value branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hTpos :=
    (avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
      x hx hxc D hD T hT hEnvelope).1
  have hw0x := avram_p3_bv_initial_value_nonnegative
    C hC w hw_cont hw0 hw_smooth hw_grad x hx hxc
  by_cases hwpos : 0 < w x
  · obtain ⟨F, M, B, hFm, hFi, hFn, hR, hBound, hFatou⟩ :=
      avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc hwpos D hD hw_nonneg hjump T hT hTpos
    exact avram_bv_env3_original_signed_fatou_grids_to_closed_cash
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos F M B
      hFm hFi hFn hR hBound hFatou
  · have hwzero : w x = 0 := le_antisymm (le_of_not_gt hwpos) hw0x
    have hRewardZero :=
      avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc hwzero D hD hw_nonneg
        hjump T hT hTpos
    apply avram_bv_env3_original_aggregate_L1_signed_strict_to_closed_cash
      X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth
      hw_grad x hx hxc D hD T hT hTpos (fun _ => (0 : ℝ))
      (integrable_zero _ _ _) (by simp)
    filter_upwards [hRewardZero] with ω hω
    dsimp at hω ⊢
    rw [hω, hwzero]
    simp
