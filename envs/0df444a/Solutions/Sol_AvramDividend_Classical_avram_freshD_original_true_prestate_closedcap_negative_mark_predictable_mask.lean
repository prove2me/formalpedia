-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_true_prestate_closedcap_negative_mark_predictable_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:26:16.222189+00:00
-- url     : https://prove2.me/submissions/5f40c425-e6a9-4db3-819c-67d64ac150d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (C : ℝ≥0∞) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r p.2 - rightLimit D r p.2) p.1
    MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ |
        0 < p.1.1 ∧ 0 ≤ Y p.1 ∧
        ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0} := by
  classical
  intro Y
  have hY : Measurable[𝓕.rightCont.predictable] Y :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD).measurable
  have hp : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => Y p.1) := hY.comp measurable_fst
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have htime : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro t
    have hs : MeasurableSet (Set.Ioi t ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        (i := t) MeasurableSet.univ
    simpa only [Set.prod_univ] using hs
  have ht : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.1.1) :=
    htime.comp measurable_fst
  have hz : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.2) := measurable_snd
  have hc := ENNReal.measurable_ofReal.comp hp
  have h0 : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | 0 < p.1.1} :=
    measurableSet_lt measurable_const ht
  have h1 : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | 0 ≤ Y p.1} :=
    measurableSet_le measurable_const hp
  have h2 : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | ENNReal.ofReal (Y p.1) ≤ C} :=
    measurableSet_le hc measurable_const
  have h3 : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | p.2 < 0} :=
    measurableSet_lt hz measurable_const
  simpa only [Set.setOf_and, Set.inter_assoc] using ((h0.inter h1).inter h2).inter h3
