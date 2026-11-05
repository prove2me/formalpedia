-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:05:25.002209+00:00
-- url     : https://prove2.me/submissions/f33dffa0-5b70-4e00-aa84-9b0fba7a7b60

import Mathlib
open Set Topology
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y : ℝ, y < 0 → w y = 0) (b : ℝ) :
∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by
  have hsub : Icc (0 : ℝ) (max b 0) ⊆ Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn (fun z : ℝ => |w z|) (Icc 0 (max b 0)) :=
    continuous_abs.comp_continuousOn (hw_cont.mono hsub)
  have hnonempty : (Icc (0 : ℝ) (max b 0)).Nonempty :=
    ⟨0, ⟨le_refl 0, le_max_right b 0⟩⟩
  obtain ⟨u, hu, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max b 0))).exists_isMaxOn
      hnonempty hcont
  refine ⟨|w u|, abs_nonneg _, ?_⟩
  intro v hv
  by_cases hvneg : v < 0
  · simp [hw_neg v hvneg]
  · exact hmax ⟨le_of_not_gt hvneg, le_trans hv (le_max_left b 0)⟩
