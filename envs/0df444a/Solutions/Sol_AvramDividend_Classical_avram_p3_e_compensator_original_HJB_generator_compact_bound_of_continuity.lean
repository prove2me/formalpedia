-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:42:38.747077+00:00
-- url     : https://prove2.me/submissions/4ad85f32-2b5a-489f-918e-5df8709a2273

import Mathlib
open Set Topology
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(H : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
(hcont : ContinuousOn H (Set.Icc a b)) :
∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc a b, |H y| ≤ K := by
  have hn : (Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  have hc : ContinuousOn (fun y : ℝ => |H y|) (Icc a b) :=
    continuous_abs.comp_continuousOn hcont
  obtain ⟨y, hy, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc a b)).exists_isMaxOn hn hc
  exact ⟨|H y|, abs_nonneg _, fun z hz => hmax hz⟩
