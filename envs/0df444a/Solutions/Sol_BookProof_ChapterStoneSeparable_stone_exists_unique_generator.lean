-- Prove2me | solution 1 for BookProof.ChapterStoneSeparable.stone_exists_unique_generator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T05:04:05.536276+00:00
-- url     : https://prove2.me/submissions/e0e3a2d3-fb2a-46d2-9e45-30d71e5f5c83

-- Generated from ChapterStoneSeparable.lean — solution of BookProof.ChapterStoneSeparable.stone_exists_unique_generator
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_ext_prime
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_eq
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_gen_stoneGroup_eq
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneSeparable



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (G : WeakMeasurableUnitaryGroup H) :
    ∃! T : UnboundedSelfAdjoint H, ∀ t : ℝ, T.stoneU t = G.U t := by

  refine ⟨G.gen, fun t => G.gen_stoneU_eq t, fun T hT => ?_⟩
  have hgroup : T.stoneGroup = G := WeakMeasurableUnitaryGroup.ext_prime hT
  rw [← T.gen_stoneGroup_eq, hgroup]
