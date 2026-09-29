-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_widen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:14:43.920428+00:00
-- url     : https://prove2.me/submissions/f433d95a-4821-4f36-b535-388085116102

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_widen
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
theorem solution {I : CertInterval} {x ε : ℝ} (hx : I.Mem x) (hε : 0 ≤ ε) :
    (I.widen ε).Mem x := ⟨by simp only [widen]; linarith [hx.1], by simp only [widen]; linarith [hx.2]⟩
