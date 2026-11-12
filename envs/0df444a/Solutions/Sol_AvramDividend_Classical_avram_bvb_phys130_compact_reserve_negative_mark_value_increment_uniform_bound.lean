-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys130_compact_reserve_negative_mark_value_increment_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:57:09.216044+00:00
-- url     : https://prove2.me/submissions/312ce6e1-2933-4fac-a593-b2b502f5188f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- A negative-mark value increment is uniformly bounded when the
nonnegative reserve remains in a fixed compact interval. -/
theorem solution (R : ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc 0 R))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b z : ℝ, 0 ≤ b → b ≤ R → z < 0 →
        |w (b + z) - w b| ≤ 2 * M := by
  have hcompact : IsCompact (w '' Icc (0 : ℝ) R) :=
    isCompact_Icc.image_of_continuousOn hw
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hcompact.isBounded
  have hpoint : ∀ a : ℝ, 0 ≤ a → a ≤ R → |w a| ≤ M := by
    intro a ha haR
    have hmem : w a ∈ w '' Icc (0 : ℝ) R :=
      ⟨a, ⟨ha, haR⟩, rfl⟩
    have hball := hM hmem
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hball
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro b z hb hbR hz
  have hb_bound : |w b| ≤ max 0 M :=
    (hpoint b hb hbR).trans (le_max_right _ _)
  have hleft : |w (b + z)| ≤ max 0 M := by
    by_cases hnonneg : 0 ≤ b + z
    · exact (hpoint (b + z) hnonneg (by linarith)).trans
        (le_max_right _ _)
    · rw [hw_neg (b + z) (lt_of_not_ge hnonneg), abs_zero]
      exact le_max_left _ _
  calc
    |w (b + z) - w b| ≤ |w (b + z)| + |w b| := abs_sub _ _
    _ ≤ max 0 M + max 0 M := add_le_add hleft hb_bound
    _ = 2 * max 0 M := by ring
