-- Prove2me | solution 1 for BookProof.ChapterH1.psi_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:22:57.235554+00:00
-- url     : https://prove2.me/submissions/34a279b6-9e24-42ae-8937-7ea826243dd8

-- Generated from ChapterH1.lean — solution of BookProof.ChapterH1.psi_resolvent
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1







open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (γ z : ℂ) (_hz : γ - z ≠ 0) :
    psi k γ (γ - z)⁻¹ = phi k z := by

  unfold psi; aesop;
