-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:04:21.10997+00:00
-- url     : https://prove2.me/submissions/895398f8-e417-4979-9be1-3e77ab191846

import Mathlib
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
-- Generated from ChapterStoneUnitary.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



variable (T : UnboundedSelfAdjoint H)


theorem solution (t : ℝ) : T.stoneU t ∈ unitary (H →L[ℂ] H) := by
  have hu : IsUnit (T.stoneU t) := by
    refine ⟨⟨T.stoneU t, T.stoneU (-t), ?_, ?_⟩, rfl⟩
    · rw [← T.stoneU_add, add_neg_cancel, T.stoneU_zero]
    · rw [← T.stoneU_add, neg_add_cancel, T.stoneU_zero]
  rw [hu.mem_unitary_iff_star_mul_self]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (T.norm_stoneU_apply t)

