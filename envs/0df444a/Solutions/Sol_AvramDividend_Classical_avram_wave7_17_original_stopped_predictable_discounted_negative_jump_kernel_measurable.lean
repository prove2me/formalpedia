-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:36:26.815781+00:00
-- url     : https://prove2.me/submissions/46e3b56b-342a-4ecd-965e-9d403a8809f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The actual discounted nonlinear negative source-jump kernel is
jointly predictable on every original predictable stopped region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
  have hY : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD).measurable
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hYlift : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => Y p.1.1 p.1.2) :=
    hY.comp measurable_fst
  have hz : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.2) := measurable_snd
  have htPred : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro a
    have hIoi : MeasurableSet[𝓕.rightCont.predictable]
        (Ioi a ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        MeasurableSet.univ
    convert hIoi using 1
    ext p
    simp
  have ht : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => (p.1.1 : ℝ)) :=
    (measurable_subtype_coe.comp htPred).comp measurable_fst
  have hdiscount : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        Real.exp (-(q * (p.1.1 : ℝ)))) :=
    ((measurable_const.mul ht).neg).exp
  have hdiff : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2)) :=
    (hw.comp (hYlift.add hz)).sub (hw.comp hYlift)
  have hregion : MeasurableSet[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      {p : (ℝ≥0 × Ω) × ℝ | p.1 ∈ E ∧ p.2 < 0} :=
    (hEm.preimage measurable_fst).inter
      (measurableSet_lt measurable_snd measurable_const)
  have hfull : Measurable[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0) :=
    Measurable.ite hregion (hdiscount.mul hdiff) measurable_const
  simpa only [Y] using hfull
