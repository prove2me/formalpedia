-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:34:58.142506+00:00
-- url     : https://prove2.me/submissions/628d5641-b27e-4552-923f-66dadce7d302

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-faithful left-limit joint measurability via the generic strict-left evaluator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s z.2 - rightLimit D s z.2)
        z.1) := by
  let F : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  have hp := postPaymentReserve_cadlag_adapted X x D hD
  have hFmeas (t : ℝ≥0) : Measurable (F t) :=
    (hp.2.2 t).mono (𝓕.rightCont.le t) le_rfl
  have hFjoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation F hFmeas
      (by intro ω t; exact hp.1 ω t)
  have hAdapt : StronglyAdapted 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => F s ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits F
      (by intro t; exact (hp.2.2 t).stronglyMeasurable)
      (by intro ω t ht; exact hp.2.1 ω t ht)
  have hzero : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s ω) (0 : ℝ≥0)) :=
    (hAdapt 0).measurable.mono (𝓕.rightCont.le 0) le_rfl
  change Measurable (fun z : ℝ≥0 × Ω =>
    Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1)
  exact avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
    F hFjoint hzero (by intro ω t ht; exact hp.2.1 ω t ht)
