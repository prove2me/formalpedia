-- Prove2me | solution 1 for BookProof.ChapterH9.norm_sub_starProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:28:00.797742+00:00
-- url     : https://prove2.me/submissions/8894846d-a880-4feb-a60d-f17541aeaab9

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem solution (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u w : E) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by
  rw [Submodule.starProjection_minimal]
  refine ciInf_le ?_ (⟨w, hw⟩ : K)
  exact ⟨0, Set.forall_mem_range.mpr fun x => norm_nonneg _⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
