-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_history_lower_survival_joint_measurable_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:20:44.801217+00:00
-- url     : https://prove2.me/submissions/7d6e05af-320a-4089-8e95-69f98f835717

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-- The genuine closed-history lower-survival event is jointly measurable in
    the sample path and the observation time, including the clock boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    MeasurableSet {z : Ω × ℝ | 0 ≤ z.2 ∧
      ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1} := by
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hInf : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) := by
    simpa [Function.comp_def] using
      (levy_running_infimum_joint_time_path_measurable X).comp hTime
  have hEq :
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1} =
      {z : Ω × ℝ | 0 ≤ z.2 ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} := by
    ext z
    simp only [mem_setOf_eq]
    have hSurv := chat04_reflected_infimum_Iic_iff_survival X
      (Real.toNNReal z.2) z.1 x
    constructor
    · rintro ⟨ht, hz⟩
      refine ⟨ht, hSurv.mpr ?_⟩
      intro s hs
      have hzs := hz s hs
      linarith
    · rintro ⟨ht, hz⟩
      refine ⟨ht, ?_⟩
      intro s hs
      have hzs := hSurv.mp hz s hs
      linarith
  rw [hEq]
  exact (measurableSet_Ici.preimage measurable_snd).inter
    (measurableSet_Iic.preimage hInf)
