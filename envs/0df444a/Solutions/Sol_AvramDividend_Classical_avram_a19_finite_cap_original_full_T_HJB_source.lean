-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_finite_cap_original_full_T_HJB_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:34:59.575436+00:00
-- url     : https://prove2.me/submissions/9ef53826-18a5-4cb4-9533-1a61c1de9ed7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn42_original_fatou_family_to_single_strict_signed_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_single_signed_budget_to_fatou_certificate
import Theorems.Thm_AvramDividend_Classical_avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-cap true-horizon budget from independent physical signed source branches. -/
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by
  have hSource : ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by
    have hw0x := avram_p3_bv_initial_value_nonnegative
      C hC w hw_cont hw0 hw_smooth hw_grad x hx hxc
    by_cases hwpos : 0 < w x
    · obtain ⟨F, M, B, hFm, hFi, hFn, hR, hBound, hFatou⟩ :=
        avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc hwpos D hD hw_nonneg
          hjump T hT hTpos
      exact avram_bv_env3_turn42_original_fatou_family_to_single_strict_signed_source
        X hBV x C D hD w hw_cont hw_neg q hq T hT
        hTpos hw_nonneg F M B hFm hFi hFn hR hBound hFatou
    · have hwzero : w x = 0 := le_antisymm (le_of_not_gt hwpos) hw0x
      have hRewardZero :=
        avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc hwzero D hD hw_nonneg
          hjump T hT hTpos
      refine ⟨fun _ => 0, integrable_zero _ _ _, by simp, ?_⟩
      filter_upwards [hRewardZero] with ω hω
      simpa [hwzero] using (le_of_eq hω)
  obtain ⟨Z, hZint, hZmean, hZpath⟩ := hSource
  have hFatou := avram_p3_grid3_original_single_signed_budget_to_fatou_certificate
    X hBV q hq w C hw_cont hw_neg x D hD hw_nonneg
    T hT hTpos Z hZint hZmean hZpath
  exact avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg q (le_of_lt hq)
    T hT hTpos hFatou
