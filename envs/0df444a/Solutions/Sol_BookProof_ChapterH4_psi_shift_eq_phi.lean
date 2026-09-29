-- Prove2me | solution 1 for BookProof.ChapterH4.psi_shift_eq_phi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:25:46.628097+00:00
-- url     : https://prove2.me/submissions/7d91d7ef-f2de-431a-a8a9-0b99b89117fa

-- Generated from ChapterH4.lean — solution of BookProof.ChapterH4.psi_shift_eq_phi
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4










open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (γ z : ℂ) (_h : γ - z ≠ 0) :
    psi k γ ((γ - z)⁻¹) = BookProof.ChapterH1.phi k z := by

  unfold psi; aesop;
