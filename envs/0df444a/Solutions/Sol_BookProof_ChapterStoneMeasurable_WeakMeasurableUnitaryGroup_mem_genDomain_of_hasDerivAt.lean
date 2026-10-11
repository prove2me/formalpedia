-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:01:03.293037+00:00
-- url     : https://prove2.me/submissions/e97b76cd-e0f1-4742-b418-e6200769109a

-- Generated from ChapterStoneConverse.lean — solution of BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup



open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

set_option maxHeartbeats 1000000 in
omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem solution {x y : H} (h : HasDerivAt (fun t : ℝ => G.U t x) y 0) :
    x ∈ G.genDomain := h.differentiableAt
