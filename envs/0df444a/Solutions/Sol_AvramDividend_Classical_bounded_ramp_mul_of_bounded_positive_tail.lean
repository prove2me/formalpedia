-- Prove2me | solution 1 for AvramDividend.Classical.bounded_ramp_mul_of_bounded_positive_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:31:34.569909+00:00
-- url     : https://prove2.me/submissions/b0b3eea2-f008-4453-bc3a-556c35cd7217

import Mathlib.Analysis.Normed.Group.Basic
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- A ramp cutoff inherits boundedness of its kernel on a positive ray. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → ‖f x‖ ≤ M) :
    BddAbove (Set.range fun x : ℝ => ‖max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x‖) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨_, hχzero, _⟩ := positive_ramp_cutoff_continuous_and_support ε hε
  refine ⟨max 0 M, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ≤ ε
  · simp [hχzero x hx, le_max_left (0 : ℝ) M]
  · have hxε : ε ≤ x := le_of_lt (lt_of_not_ge hx)
    have hχ0 : 0 ≤ max (0 : ℝ) (min 1 ((x - ε) / ε)) := le_max_left _ _
    have hχ1 : max (0 : ℝ) (min 1 ((x - ε) / ε)) ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    calc
      ‖max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x‖ = max (0 : ℝ) (min 1 ((x - ε) / ε)) * ‖f x‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hχ0]
      _ ≤ ‖f x‖ := mul_le_of_le_one_left (norm_nonneg _) hχ1
      _ ≤ M := hM x hxε
      _ ≤ max 0 M := le_max_right _ _
