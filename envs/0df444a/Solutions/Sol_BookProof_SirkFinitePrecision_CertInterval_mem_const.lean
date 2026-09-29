-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:07:52.772958+00:00
-- url     : https://prove2.me/submissions/d6fe1f33-c7ca-4917-9afb-d9e0eacd020a

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_const
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
theorem solution (c : ℝ) : (CertInterval.mk c c).Mem c := ⟨le_rfl, le_rfl⟩
