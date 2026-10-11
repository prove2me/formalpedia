-- Prove2me | solution 1 for BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:01:17.769513+00:00
-- url     : https://prove2.me/submissions/7af1d495-faa6-42ba-9fb6-697643309454
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStoneConverse.lean — solution of BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_apply_eq_domain
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup



open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : G.gen.stoneU t = G.U t := by

  have hall := Continuous.ext_on G.denseDomain (G.gen.stoneU t).continuous (G.U t).continuous
    (fun y hy => G.gen_stoneU_apply_eq_domain t ⟨y, hy⟩)
  ext x
  exact congrFun hall x
