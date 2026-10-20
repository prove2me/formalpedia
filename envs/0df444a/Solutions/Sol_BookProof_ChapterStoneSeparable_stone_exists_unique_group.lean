-- Prove2me | solution 1 for BookProof.ChapterStoneSeparable.stone_exists_unique_group
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T05:04:04.436667+00:00
-- url     : https://prove2.me/submissions/46bc6389-9256-4ece-9724-29cb1e3daf48

-- Generated from ChapterStoneSeparable.lean — solution of BookProof.ChapterStoneSeparable.stone_exists_unique_group
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneSeparable_eq_stoneU_of_hasDerivAt
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_ext_prime
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_zero
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneTheorem
open BookProof.ChapterStoneSeparable



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) :
    ∃! G : WeakMeasurableUnitaryGroup H,
      ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0 := by

  refine ⟨T.stoneGroup, fun x => T.hasDerivAt_stoneU_zero x, fun G hG => ?_⟩
  exact WeakMeasurableUnitaryGroup.ext_prime (fun t => eq_stoneU_of_hasDerivAt T G hG t)
