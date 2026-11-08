-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_zero_extension_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:29:39.555427+00:00
-- url     : https://prove2.me/submissions/43bede19-e083-4a5b-ae7b-3704abc5bac0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-! Exact affine zero-extension boundary conditions for A19. -/

theorem solution :
    ContinuousOn (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y) (Ici 0) ∧
    0 ≤ (if (0 : ℝ) < 0 then (0 : ℝ) else 1 + 0) ∧
    (∀ y : ℝ, y < 0 → (if y < 0 then (0 : ℝ) else 1 + y) = 0) := by
  have hcont : ContinuousOn (fun y : ℝ => 1 + y) (Ici 0) :=
    (continuous_const.add continuous_id).continuousOn
  refine ⟨?_, by norm_num, ?_⟩
  · apply hcont.congr
    intro y hy
    have hnonneg : 0 ≤ y := hy
    simp [not_lt.mpr hnonneg]
  · intro y hy
    simp [hy]
