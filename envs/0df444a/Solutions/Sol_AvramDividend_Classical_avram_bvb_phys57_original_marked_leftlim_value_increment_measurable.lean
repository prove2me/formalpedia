-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys57_original_marked_leftlim_value_increment_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:40:11.159974+00:00
-- url     : https://prove2.me/submissions/73e20f5d-84d8-4b95-91f9-bbaea9afa96a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original predictable left limits give a jointly measurable marked value increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) := by
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change Measurable[(𝓕.rightCont.predictable).prod
    (inferInstance : MeasurableSpace ℝ)]
    (fun p : (ℝ≥0 × Ω) × ℝ =>
      w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))
  have hUm : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => U p.1 p.2) :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD).measurable
  have hw : Measurable w :=
    avram_wave8_22_original_BV_value_measurable_of_positive_continuity
      w hw_cont hw_neg
  have hUmark : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => U p.1.1 p.1.2) :=
    hUm.comp measurable_fst
  have hMark : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.2) := measurable_snd
  exact (hw.comp (hUmark.add hMark)).sub (hw.comp hUmark)
