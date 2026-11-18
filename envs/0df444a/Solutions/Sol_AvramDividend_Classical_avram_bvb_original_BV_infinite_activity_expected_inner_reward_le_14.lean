-- Prove2me | solution 14 for AvramDividend.Classical.avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:51:35.959876+00:00
-- url     : https://prove2.me/submissions/9dd4d993-ad0c-4e63-bf29-2d2f4142eca0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_infinite_activity_topcap_original_strict_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_infinite_activity_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  intro δ S F n
  by_cases htop : C = ⊤
  · simpa only [F, δ, S] using
      (avram_bvb_infinite_activity_topcap_original_strict_reward_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        T hT hInfinite htop n)
  · let Y : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    have hYI : Integrable Y P := by
      simpa only [Y, S] using
        (avram_p3_bv_original_prebudget_L1
          X hBV x C D hD w hw_cont hw_neg q hq.le T hT.le)
    have hFI : Integrable (F n) P := by
      simpa only [F, δ, S] using
        (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
          X hBV x C D hD w hw_cont hw_neg q hq T hT n)
    have hPrefix : ∀ ω, F n ω ≤ Y ω := by
      intro ω
      have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
      have hS : (S : ℝ) = T := rfl
      have hFiniteClosed :
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
        simpa only [hS] using
          (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
            D hDiv ω (ruinTime X x D ω) S q hq.le)
      have hFinStrict :
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
        apply ne_of_lt
        exact lt_of_le_of_lt (lintegral_mono_set
          (show paymentTimes (ruinTime X x D ω) ∩ Iio T ⊆
            paymentTimes (ruinTime X x D ω) ∩ Iic T from
              inter_subset_inter_right _ Iio_subset_Iic_self)) hFiniteClosed
      have hδ : 0 ≤ δ n := by
        dsimp [δ]
        positivity
      have hCut : T - δ n ≤ T := sub_le_self T hδ
      have hCashMono :
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
        apply ENNReal.toReal_mono hFinStrict
        exact lintegral_mono_set
          (inter_subset_inter_right _ (Iio_subset_Iio hCut))
      simpa only [F, Y, add_comm] using add_le_add_right hCashMono
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    have hMean : (∫ ω, Y ω ∂P) ≤ w x := by
      simpa only [Y, S] using
        (avram_bv_finite734_infinite_activity_original_full_T_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
          T hT.le hT htop hInfinite)
    exact (integral_mono hFI hYI hPrefix).trans hMean
