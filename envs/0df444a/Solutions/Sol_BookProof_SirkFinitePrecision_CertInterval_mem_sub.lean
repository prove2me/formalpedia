-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:13:35.329351+00:00
-- url     : https://prove2.me/submissions/2582cdd2-c8ae-4a30-bdd1-6cbb4f71c771

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_sub
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
theorem solution {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x - y) := ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩
