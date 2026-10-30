-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:16:31.503343+00:00
-- url     : https://prove2.me/submissions/19f43b1f-7cbb-4145-985c-44fb8b6da7ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The entire actual shifted Lévy reserve survives a random real
residual horizon in a jointly measurable source path-clock event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (a : ℝ) :
    MeasurableSet {z : Ω × ℝ |
      0 ≤ z.2 ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)} := by
  classical
  let age : Ω × ℝ → ℝ≥0 := fun z =>
    Real.toNNReal (z.2 - (τ z.1 : ℝ))
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω s =>
    X.X (τ ω + s) ω - X.X (τ ω) ω
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun u f =>
    if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
        0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
    then 1 else 0
  have hage : Measurable age := by
    dsimp [age]
    fun_prop
  have hY : Measurable Y :=
    avram_ws01e_b_randomAge_whole_shiftedPath_measurable X τ hτ
  have hH := avram_ws01h_rational_age_fullPath_survival_reward_measurable a
  have hObs : Measurable (fun z : Ω × ℝ => H (age z) (Y z.1)) :=
    hH.comp (hage.prodMk (hY.comp measurable_fst))
  have hGrid : MeasurableSet
      {z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
          0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)} := by
    have heq :
      {z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
          0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)} =
      {z : Ω × ℝ | H (age z) (Y z.1) = 1} := by
      ext z
      simp only [H, Set.mem_setOf_eq, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
    rw [heq]
    exact measurableSet_eq_fun hObs measurable_const
  have hJoint := chat04_levy_joint_time_state_measurable X
  have hτp : Measurable (fun z : Ω × ℝ => τ z.1) :=
    hτ.comp measurable_fst
  have hStart : Measurable (fun z : Ω × ℝ => X.X (τ z.1) z.1) :=
    hJoint.comp (hτp.prodMk measurable_fst)
  have hEnd : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1 + age z) z.1) :=
    hJoint.comp ((hτp.add hage).prodMk measurable_fst)
  have hTerminal : MeasurableSet
      {z : Ω × ℝ | 0 ≤ a +
        (X.X (τ z.1 + age z) z.1 - X.X (τ z.1) z.1)} :=
    measurableSet_le measurable_const
      (measurable_const.add (hEnd.sub hStart))
  have hPos : MeasurableSet {z : Ω × ℝ | 0 ≤ z.2} :=
    measurableSet_le measurable_const measurable_snd
  have hEvent : {z : Ω × ℝ |
      0 ≤ z.2 ∧ ∀ u : ℝ≥0, u ≤ age z →
        0 ≤ a + Y z.1 u} =
      {z : Ω × ℝ | 0 ≤ z.2} ∩
      ({z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
           0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)} ∩
       {z : Ω × ℝ | 0 ≤ a +
         (X.X (τ z.1 + age z) z.1 - X.X (τ z.1) z.1)}) := by
    ext z
    have hiff := (chat04_random_reserve_shifted_closed_survival_grid_iff
      X (fun _ : Ω => a) z.1 (τ z.1) (age z))
    change (0 ≤ z.2 ∧ ∀ u : ℝ≥0, u ≤ age z →
      0 ≤ a + Y z.1 u) ↔
      (0 ≤ z.2 ∧
       (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
         0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) ∧
       0 ≤ a + (X.X (τ z.1 + age z) z.1 - X.X (τ z.1) z.1))
    exact and_congr_right (fun _ => hiff)
  change MeasurableSet
    {z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ u : ℝ≥0, u ≤ age z →
      0 ≤ a + Y z.1 u}
  rw [hEvent]
  exact hPos.inter (hGrid.inter hTerminal)
