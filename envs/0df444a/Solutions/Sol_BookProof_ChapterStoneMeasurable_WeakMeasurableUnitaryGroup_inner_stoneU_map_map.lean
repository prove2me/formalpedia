-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:16:52.038725+00:00
-- url     : https://prove2.me/submissions/cfc9f381-980a-4d44-add5-70dc9180b66b

import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)


theorem solution (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H)
    (u : ℝ) (a b : H) : ⟪T.stoneU u a, T.stoneU u b⟫_ℂ = ⟪a, b⟫_ℂ := by
  have hu : IsUnit (T.stoneU u) := by
    refine ⟨⟨T.stoneU u, T.stoneU (-u), ?_, ?_⟩, rfl⟩
    · rw [← T.stoneU_add, add_neg_cancel, T.stoneU_zero]
    · rw [← T.stoneU_add, neg_add_cancel, T.stoneU_zero]
  have hm : T.stoneU u ∈ unitary (H →L[ℂ] H) := by
    rw [hu.mem_unitary_iff_star_mul_self]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (T.norm_stoneU_apply u)
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary hm a b

