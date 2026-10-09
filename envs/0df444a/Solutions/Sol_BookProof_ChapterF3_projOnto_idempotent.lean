-- Prove2me | solution 1 for BookProof.ChapterF3.projOnto_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:59:34.286143+00:00
-- url     : https://prove2.me/submissions/e2ed3a77-e2fa-4383-9056-03dc0e7610f5

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.projOnto_idempotent
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) :
    projOnto ψ (projOnto ψ s) = projOnto ψ s := by

  simp [ hψ, inner_self_eq_norm_sq_to_K ]
