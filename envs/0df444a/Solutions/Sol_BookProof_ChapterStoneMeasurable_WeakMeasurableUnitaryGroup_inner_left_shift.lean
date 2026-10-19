-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:16:32.151004+00:00
-- url     : https://prove2.me/submissions/198bd4da-90d4-4daf-a49d-dc609a931531

import Mathlib
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneConverse
-- Generated from ChapterStoneMeasurable.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (G : WeakMeasurableUnitaryGroup H)


theorem solution (s t : ℝ) (x y : H) :
    ⟪ y, G.U s (G.U t x) ⟫_ℂ = ⟪ G.U (-s) y, G.U t x ⟫_ℂ := by
  exact G.inner_adjoint s y (G.U t x)

