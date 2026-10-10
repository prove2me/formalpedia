-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.adj_closure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:02:47.609984+00:00
-- url     : https://prove2.me/submissions/c1a7e235-3c91-45af-b8c4-bafee8b7fad2

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.adj_closure
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
import Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_lie_adj_leibniz
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]


@[simp] private theorem adjVar_apply (θ X : L) : adjVar θ X = ⁅X, θ⁆ := rfl

set_option maxHeartbeats 1000000 in
theorem solution (θ η X : L) :
    adjVar η (adjVar θ X) - adjVar θ (adjVar η X) = adjVar ⁅θ, η⁆ X := by

  simp only [adjVar_apply]
  rw [← lie_adj_leibniz X η θ, ← lie_skew θ η]
  simp
