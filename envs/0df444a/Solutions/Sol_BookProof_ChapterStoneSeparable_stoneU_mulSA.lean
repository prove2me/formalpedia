-- Prove2me | solution 1 for BookProof.ChapterStoneSeparable.stoneU_mulSA
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T05:04:09.185982+00:00
-- url     : https://prove2.me/submissions/fb1a3bd9-bc03-4631-a484-48578b4b882b

-- Generated from ChapterStoneSeparable.lean — solution of BookProof.ChapterStoneSeparable.stoneU_mulSA
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Theorems.Thm_BookProof_ChapterStoneSeparable_eq_stoneU_of_hasDerivAt
import Theorems.Thm_BookProof_ChapterStoneSeparable_hasDerivAt_phaseGroup
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterStoneSeparable



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) :
    (mulSA f).stoneU t psi = phaseUnitary f (-t) psi := by

  have h := eq_stoneU_of_hasDerivAt (mulSA f) (phaseGroup f) (hasDerivAt_phaseGroup f) t
  exact congrArg (fun L : L2Z →L[ℂ] L2Z => L psi) h.symm
