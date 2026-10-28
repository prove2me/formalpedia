-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_joint_random_horizon_strict_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:21:26.876586+00:00
-- url     : https://prove2.me/submissions/915baf6e-1a50-473d-9d6e-a28ac2cc1c74

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Measurable (fun z : ℝ≥0 × Ω => f z.1 z.2))
    (hcont : ∀ ω : Ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun t => f t ω) (Set.Ici s) s)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : Ω × Θ → ℝ) (ha : Measurable a) :
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧ f s z.1 < a z} := by
  have key : {z : Ω × Θ | ∃ s : ℝ≥0, s ≤ e z.2 ∧ f s z.1 < a z} =
      ⋃ n : ℕ, ⋃ k : Fin ((2 : ℕ) ^ n + 1),
        {z : Ω × Θ | f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * e z.2) z.1 < a z} := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion]
    rcases eq_zero_or_pos (e z.2) with h | h
    · rw [h]
      simp only [nonpos_iff_eq_zero, exists_eq_left, mul_zero]
      exact ⟨fun h => ⟨0, 0, h⟩, fun ⟨_, _, h⟩ => h⟩
    · exact avram_ws01e_b_right_continuous_strict_dyadic_grid_event
        (fun t => f t z.1) (e z.2) h (hcont z.1) (a z)
  rw [key]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k => ?_
  have hg : Measurable (fun z : Ω × Θ => f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * e z.2) z.1) :=
    hf.comp ((measurable_const.mul (he.comp measurable_snd)).prodMk measurable_fst)
  exact measurableSet_lt hg ha
