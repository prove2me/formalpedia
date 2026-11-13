-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_BV_C1_discounted_compact_kernel_intensity_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:04:35.533418+00:00
-- url     : https://prove2.me/submissions/68f10985-b217-432a-b0d5-97ff87962bba

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_positive_band_analytic_certificate
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (T : ℝ≥0) (μ : @Measure (ℝ≥0 × Ω) 𝓕.rightCont.predictable) (hμ : μ univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : ℝ≥0 × Ω → ℝ := fun p => if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => A p.1 *
      (if Y p.1 ∈ Icc a b ∧ p.2 < 0 then w (Y p.1 + p.2) - w (Y p.1) else 0)
    Measurable[𝓕.rightCont.predictable] Y ∧
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] G ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  classical
  intro Y A G
  obtain ⟨hwmeas, _, L, R, hL, hR, hLip, hW⟩ :=
    avram_chat24_C1_positive_band_analytic_certificate w hw_cont hw_neg hw a b 0 q ha hab
  have hY : Measurable[𝓕.rightCont.predictable] Y :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD).measurable
  have hA : Measurable[𝓕.rightCont.predictable] A :=
    (avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      (𝓕 := 𝓕) q hq T).1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hYm : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => Y p.1) := hY.comp measurable_fst
  have hG : Measurable G := (hA.comp measurable_fst).mul
    (((hwmeas.comp (hYm.add measurable_snd)).sub (hwmeas.comp hYm)).ite
      ((measurableSet_Icc.preimage hYm).inter (measurableSet_Iio.preimage measurable_snd)) measurable_const)
  have hneg : -(a / 2) = -a / 2 := by ring
  have hfar : X.ν (Iic (-a / 2)) < ⊤ := by
    simpa only [hneg] using levy_negative_mass_away_from_zero_finite X (a / 2) (by linarith)
  refine ⟨hY, hG, ?_⟩
  apply avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
    X hBV x D w q hq a b L R ha ha2 hab hL hR hLip hW μ hμ
    {p | p.1 ≤ T ∧ Y p ∈ Icc a b} (fun p hp => hp.2)
    hfar G
    (fun p => by dsimp [G, A]; split_ifs <;> simp_all [Y]) hG.aestronglyMeasurable
