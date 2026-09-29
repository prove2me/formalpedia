-- Prove2me | solution 2 for FamousTheorems.szemeredi_regularity_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:55:57.064404+00:00
-- url     : https://prove2.me/submissions/671eb671-cd12-4b46-b6f9-a7fbd4244db7

import Mathlib

theorem solution {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type*) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α → ∃ P : Finpartition (Finset.univ : Finset α),
        P.IsEquipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ M ∧ P.IsUniform G ε :=
  ⟨SzemerediRegularity.bound ε l, fun _ _ _ G _ hl => szemeredi_regularity G hε hl⟩
