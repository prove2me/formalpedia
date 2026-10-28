-- Prove2me | solution 1 for AvramDividend.Classical.levy_running_infimum_joint_time_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:36:00.889337+00:00
-- url     : https://prove2.me/submissions/b699edb2-5ab4-4501-b528-3e7f39b7079c

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_chat04_lower_clock_weak_survival_past_ws01a
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine negative running infimum is jointly measurable in time and path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.1 ∧ y = X.X s z.2}) := by
  apply measurable_of_Iic
  intro a
  have heq :
      (fun z : ℝ≥0 × Ω =>
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.1 ∧ y = X.X s z.2}) ⁻¹' Iic a =
      {z : ℝ≥0 × Ω |
        (z.1 : ℝ≥0∞) ≤ twoSidedExitDownTime X (-a) z.2 ∧
        -a ≤ X.X z.1 z.2} := by
    ext ⟨t, ω⟩
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    have hb := levy_path_bddBelow_finite_horizon X t ω
    have hsurv := lower_survival_running_infimum_equiv X t ω hb a
    have hclock := chat04_lower_clock_weak_survival_past_ws01a X (-a) ω t
    constructor
    · intro hinf
      have hall : ∀ s : ℝ≥0, s ≤ t → 0 ≤ a + X.X s ω :=
        hsurv.mpr (by linarith)
      constructor
      · apply hclock.mpr
        intro s hs
        have h := hall s hs.le
        linarith
      · have h := hall t le_rfl
        linarith
    · rintro ⟨hpre, hend⟩
      have hpast := hclock.mp hpre
      have hall : ∀ s : ℝ≥0, s ≤ t → 0 ≤ a + X.X s ω := by
        intro s hs
        rcases lt_or_eq_of_le hs with hlt | heq
        · have h := hpast s hlt
          linarith
        · subst s
          linarith
      have h := hsurv.mp hall
      linarith
  rw [heq]
  have htime : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp measurable_fst
  have hclock : Measurable
      (fun z : ℝ≥0 × Ω => twoSidedExitDownTime X (-a) z.2) :=
    ((chat03_both_named_passage_clocks_measurable X (-a) 0).2).comp
      measurable_snd
  have hstate : Measurable
      (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  exact (measurableSet_le htime hclock).inter
    (measurableSet_le measurable_const hstate)
