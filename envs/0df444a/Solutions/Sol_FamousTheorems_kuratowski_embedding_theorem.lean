-- Prove2me | solution 1 for FamousTheorems.kuratowski_embedding_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:27.400334+00:00
-- url     : https://prove2.me/submissions/c43f55b2-65fa-45f3-9500-a82836aff6dd

import Mathlib

theorem solution (α : Type*) [MetricSpace α] [TopologicalSpace.SeparableSpace α] :
    ∃ f : α → lp (fun _ : ℕ => ℝ) ⊤, Isometry f :=
  ⟨kuratowskiEmbedding α, kuratowskiEmbedding.isometry α⟩
