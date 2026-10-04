-- Prove2me | solution 1 for BookProof.ChapterH9.norm_sub_starProjection_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:07.261613+00:00
-- url     : https://prove2.me/submissions/9e019194-5c5d-456f-853c-2efec32e54b5

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem solution (K L : Submodule ℂ E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) (v : E) :
    ‖v - L.starProjection v‖ ≤ ‖v - K.starProjection v‖ := by
  rw [Submodule.starProjection_minimal (U := L)]
  refine ciInf_le ?_ (⟨K.starProjection v, hKL (K.starProjection_apply_mem v)⟩ : L)
  exact ⟨0, Set.forall_mem_range.mpr fun x => norm_nonneg _⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
