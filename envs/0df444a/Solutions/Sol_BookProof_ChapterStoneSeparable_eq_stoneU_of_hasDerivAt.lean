-- Prove2me | solution 1 for BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T05:04:03.147647+00:00
-- url     : https://prove2.me/submissions/ae42ad17-6c60-4256-a344-252aebbcfd0f

-- Generated from ChapterStoneSeparable.lean — solution of BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneSeparable_gen_eq_of_hasDerivAt
import Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_eq
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneSeparable



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) (G : WeakMeasurableUnitaryGroup H)
    (h : ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0)
    (t : ℝ) : G.U t = T.stoneU t := by

  rw [← G.gen_stoneU_eq t, gen_eq_of_hasDerivAt T G h]
