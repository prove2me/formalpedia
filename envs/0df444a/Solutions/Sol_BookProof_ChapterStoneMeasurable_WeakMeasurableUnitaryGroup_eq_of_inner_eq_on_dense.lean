-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:16:43.964258+00:00
-- url     : https://prove2.me/submissions/6d902d12-d5c9-48d4-bcce-b0756ee374fb

import Mathlib
import Definitions.Def_ChapterStoneConverse
-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)


theorem solution {D : Set H} (hD : Dense D) {v w : H}
    (h : ∀ z ∈ D, ⟪z, v⟫_ℂ = ⟪z, w⟫_ℂ) : v = w := by
  have hS : IsClosed {z : H | ⟪z, v - w⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : D ⊆ {z : H | ⟪z, v - w⟫_ℂ = 0} := by
    intro z hz
    simp only [Set.mem_setOf_eq, inner_sub_right, h z hz, sub_self]
  have hall : ∀ z : H, ⟪z, v - w⟫_ℂ = 0 := by
    intro z
    have : z ∈ closure D := by rw [hD.closure_eq]; trivial
    exact (closure_minimal hsub hS) this
  have := hall (v - w)
  rw [inner_self_eq_zero, sub_eq_zero] at this
  exact this

