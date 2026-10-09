-- Prove2me | solution 1 for BookProof.ChapterF3.projOnto_eq_starProjection
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:59:47.211016+00:00
-- url     : https://prove2.me/submissions/071d12a8-87fa-4658-8c08-8e62db5c7bb4

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.projOnto_eq_starProjection
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) :
    projOnto ψ s = (Submodule.span ℂ {ψ}).starProjection s := by

  rw [ Submodule.starProjection_singleton ] ; aesop
