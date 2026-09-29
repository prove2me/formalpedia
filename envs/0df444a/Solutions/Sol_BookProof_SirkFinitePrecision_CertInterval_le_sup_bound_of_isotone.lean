-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:04:37.76237+00:00
-- url     : https://prove2.me/submissions/0e3a2d2b-f760-45b5-a4c1-263c466ea9c5

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.le_sup_bound_of_isotone
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
theorem solution {α : Type*} (f : α → ℝ) (S : Set α) (I : CertInterval)
    (hF : ∀ z ∈ S, I.Mem (f z)) {z : α} (hz : z ∈ S) :
    f z ≤ I.hi := (hF z hz).2
