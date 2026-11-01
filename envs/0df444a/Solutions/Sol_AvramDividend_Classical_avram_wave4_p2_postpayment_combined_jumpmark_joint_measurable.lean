-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:52:26.357601+00:00
-- url     : https://prove2.me/submissions/07425606-c49a-4664-834b-8cf4bd3cc36e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_exact_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The actual source jump minus its simultaneous dividend atom is a
jointly measurable marked field, with zero assigned at initial time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        (X.X z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) -
          (rightLimit D z.1 z.2 - D z.1 z.2)
      else 0) := by
  have hp := postPaymentReserve_cadlag_adapted X x D hD
  let F : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  have hsections (t : ℝ≥0) : Measurable (F t) := by
    exact (hp.2.2 t).mono (𝓕.rightCont.le t) le_rfl
  have hright : ∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => F s ω) (Ici t) t := by
    intro ω t
    exact hp.1 ω t
  have hF : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation F hsections hright
  have hleft : Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1) :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable X x D hD
  have hmasked : Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        F z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1
      else 0) :=
    Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      (hF.sub hleft) measurable_const
  have hEq : (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        (X.X z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) -
          (rightLimit D z.1 z.2 - D z.1 z.2)
      else 0) =
    (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        F z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1
      else 0) := by
    funext z
    by_cases hz : 0 < z.1
    · simp only [if_pos hz]
      exact (avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
        X x D hD z.2 z.1 hz).symm
    · simp [hz]
  rw [hEq]
  exact hmasked
