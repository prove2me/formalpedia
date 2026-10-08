-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:55:53.338025+00:00
-- url     : https://prove2.me/submissions/265aca91-8b10-4e6d-833a-1a7b564522f2

import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberCard

open BookProof.ChapterFreeFieldBornQuotient BookProof.ChapterFreeFieldBornFiberCard

theorem solution {n : ℕ} {p : ↥(stdSimplex ℝ (Fin n))}
    (hp : ∀ k, 0 < (p : Fin n → ℝ) k) :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ n := by
  rw [← Nat.card_congr (bornFiberEquiv hp)]
  simp

#print axioms solution
