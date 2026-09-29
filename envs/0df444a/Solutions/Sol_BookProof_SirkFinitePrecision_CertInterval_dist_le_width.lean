-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.dist_le_width
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:01:51.079794+00:00
-- url     : https://prove2.me/submissions/cff9661d-8fe0-4db7-9085-297928a08eba

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.dist_le_width
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
theorem solution {I : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : I.Mem y) :
    |x - y| ≤ I.width := by

  rw [abs_le]
  exact ⟨by simp only [width]; linarith [hx.1, hy.2],
    by simp only [width]; linarith [hx.2, hy.1]⟩
