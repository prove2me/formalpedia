-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:12:26.480551+00:00
-- url     : https://prove2.me/submissions/ebfe2590-0b99-4db1-9ddc-564aac8e2913

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded
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
theorem solution {x lo hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    (CertInterval.mk lo hi).Mem x := ⟨h1, h2⟩
