-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_true_stopped_discount_fullnegative_value_product_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:45:02.098288+00:00
-- url     : https://prove2.me/submissions/50b3f1a3-889c-4a59-8f78-af7e39c3b677

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        ((if p.1.1 ≤ (n : ℝ≥0)
            then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) *
          ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
            then (1 : ℝ) else 0) *
           (w (Y p.1 + p.2) - w (Y p.1)))) := by
  classical
  intro Y
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hr : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD
  have hm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
          then (1 : ℝ) else 0) *
          (w (Y p.1 + p.2) - w (Y p.1))) := by
    simpa only [Y] using
      (avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
        X x D hD w hw (ruinTime X x D) hr)
  have hd : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ (n : ℝ≥0)
          then Real.exp (-(q * (p.1 : ℝ))) else 0) *
          (if (p.1 : ℝ≥0∞) ≤ (σ p.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) :=
    (avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
      (fun ω => (σ ω : ℝ≥0∞)) hσstop q hq (n : ℝ≥0)).1
  exact (hd.comp measurable_fst).mul hm
