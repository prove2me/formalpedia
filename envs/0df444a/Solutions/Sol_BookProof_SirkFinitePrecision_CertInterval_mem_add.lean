-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:06:30.7995+00:00
-- url     : https://prove2.me/submissions/9872fb18-6e12-4d09-8a3f-98d3732c8404

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_add
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
    (I.add J).Mem (x + y) := ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩
