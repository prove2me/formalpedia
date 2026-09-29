-- Prove2me | solution 2 for FamousTheorems.triangle_removal_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:55:57.216184+00:00
-- url     : https://prove2.me/submissions/c9bd653e-b10f-4ac7-a176-67db8e24ff77

import Mathlib

theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (α : Type*) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      ((G.cliqueFinset 3).card : ℝ) < δ * Fintype.card α ^ 3 →
        ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
          ((G.edgeFinset.card : ℝ) - G'.edgeFinset.card) < ε * (Fintype.card α ^ 2 : ℕ) ∧ G'.CliqueFree 3 :=
  ⟨_, SimpleGraph.triangleRemovalBound_pos hε, fun _ _ _ _ _ hG => SimpleGraph.triangle_removal hG⟩
