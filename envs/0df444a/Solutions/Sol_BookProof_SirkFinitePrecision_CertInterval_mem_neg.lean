-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:10:44.609586+00:00
-- url     : https://prove2.me/submissions/afe376f7-c717-4623-be3a-e6016d612e2d

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_neg
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {I : CertInterval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
