-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_negative_zero_uniform_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:02:15.1964+00:00
-- url     : https://prove2.me/submissions/2184e1ca-49ac-4d73-8c17-8451428caee4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A continuous nonnegative-reserve test vanishing on negative reserves
has a uniform value bound on every left-unbounded reserve strip. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by
  have hsub : Icc (0 : ℝ) b ⊆ Ici 0 := by
    intro y hy
    exact hy.1
  have hcont : ContinuousOn (fun y : ℝ => |w y|) (Icc 0 b) :=
    (hw_cont.mono hsub).abs
  have hcompact : IsCompact ((fun y : ℝ => |w y|) '' Icc 0 b) :=
    isCompact_Icc.image_of_continuousOn hcont
  obtain ⟨R, hR⟩ := hcompact.bddAbove
  have hzero : |w 0| ≤ R := by
    apply hR
    exact Set.mem_image_of_mem _ ⟨le_refl _, hb⟩
  have hR0 : 0 ≤ R := (abs_nonneg (w 0)).trans hzero
  refine ⟨R, hR0, ?_⟩
  intro v hv
  by_cases hvneg : v < 0
  · simpa [hw_neg v hvneg] using hR0
  · have hv0 : 0 ≤ v := le_of_not_gt hvneg
    apply hR
    exact Set.mem_image_of_mem _ ⟨hv0, hv⟩
