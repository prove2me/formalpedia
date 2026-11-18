-- Prove2me | solution 12 for AvramDividend.Classical.avram_p3_bv_original_source_signed_fatou_grid_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:11:59.015277+00:00
-- url     : https://prove2.me/submissions/98fb553c-29f6-45f1-83e2-ad5383d389c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
import Theorems.Thm_AvramDividend_Classical_avram_bv_topcap_original_full_T_strict_cash_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨F, hFM, hFI, hFnonneg, hFEq⟩ :=
    avram_p3_bv_original_strict_reward_measurable_version
      X hBV x C D hD w hw_cont hw_neg q hq.le T hT hTpos hw_nonneg
  have hStrictMean : (∫ ω, Strict ω ∂P) ≤ w x := by
    by_cases hTop : C = ⊤
    · simpa only [Strict, S] using
        (avram_bv_topcap_original_full_T_strict_cash_expected_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos hTop)
    · simpa only [Strict, S] using
        (avram_a19_finite_cap_original_full_T_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos hTop)
  have hFMean : (∫ ω, F ω ∂P) ≤ w x := by
    rw [integral_congr_ae hFEq]
    exact hStrictMean
  refine ⟨(fun _ => F), (fun _ _ => 0),
    (fun _ ω => F ω - w x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hFM
  · intro n
    exact hFI
  · intro n
    exact hFnonneg
  · intro n
    have hB : Integrable (fun ω => F ω - w x) P := by
      convert hFI.sub (integrable_const (w x)) using 1
      funext ω
      simp
    constructor
    · change Integrable (fun ω => (0 : ℝ) + (F ω - w x)) P
      simpa only [zero_add] using hB
    · have hBmean : (∫ ω, F ω - w x ∂P) ≤ 0 := by
        rw [integral_sub hFI (integrable_const _)]
        simpa using (sub_nonpos.mpr hFMean)
      change (∫ ω, (0 : ℝ) + (F ω - w x) ∂P) ≤ 0
      simpa only [zero_add] using hBmean
  · intro n
    filter_upwards [] with ω
    simp
  · filter_upwards [hFEq] with ω hEq
    simpa [hEq, Strict, S] using (le_refl (ENNReal.ofReal (F ω)))
