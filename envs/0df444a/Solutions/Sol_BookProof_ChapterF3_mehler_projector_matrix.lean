-- Prove2me | solution 1 for BookProof.ChapterF3.mehler_projector_matrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T15:54:16.518189+00:00
-- url     : https://prove2.me/submissions/6b8087e8-0651-454f-9894-a6f419dc7038

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.mehler_projector_matrix
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

set_option maxHeartbeats 1000000 in

theorem solution (v xi xj : E') :
    inner (𝕜 := ℂ) xi (projOnto v xj)
      = (starRingEnd ℂ) (inner (𝕜 := ℂ) v xi) * inner (𝕜 := ℂ) v xj := by
  simp [ projOnto ];
  ring

end
