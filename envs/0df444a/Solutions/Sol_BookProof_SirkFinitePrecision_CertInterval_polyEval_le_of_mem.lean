-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:14:51.361587+00:00
-- url     : https://prove2.me/submissions/bb2b5363-0658-4c9f-afdb-0e6877876385

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.polyEval_le_of_mem
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_evalHorner
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    polyEval cs x ≤ (evalHorner cs I).hi := (mem_evalHorner cs I x hx).2
