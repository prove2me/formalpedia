-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_global_predictable_generator_mark_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:31:36.742616+00:00
-- url     : https://prove2.me/submissions/c7d72165-8f0e-4ce6-b506-1c04ec1a349e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The genuine source compensated Lévy mark kernel is measurable for the
original right-continuous predictable filtration and source mark Borel space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand w
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) p.2) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
  have hpred : IsStronglyPredictable 𝓕.rightCont Y :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hY : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    hpred.measurable
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hd : Measurable (deriv w) := measurable_deriv w
  have hYlift : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => Y p.1.1 p.1.2) :=
    hY.comp measurable_fst
  have hz : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.2) :=
    measurable_snd
  have hi : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2) :=
    (measurable_const.indicator measurableSet_Ioo).comp hz
  have hk : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2) -
          deriv w (Y p.1.1 p.1.2) * p.2 *
            (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2) :=
    ((hw.comp (hYlift.add hz)).sub (hw.comp hYlift)).sub
      (((hd.comp hYlift).mul hz).mul hi)
  simpa only [Y, SpectrallyNegativeLevy.generatorIntegrand] using hk
