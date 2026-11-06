-- Prove2me | solution 1 for BookProof.ChapterF3.projOnto_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T13:18:49.109014+00:00
-- url     : https://prove2.me/submissions/2a2e518c-795d-48f6-ad62-1e4a87d5e6b9

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.projOnto_isSymmetric
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in

theorem solution (ψ : E) (x y : E) :
    inner (𝕜 := ℂ) (projOnto ψ x) y = inner (𝕜 := ℂ) x (projOnto ψ y) := by
  simp [projOnto]

/-
**F2.6** (identification with the Mathlib projection): for a unit `ψ`,
`projOnto ψ` is the orthogonal projection onto the line `ℂ ∙ ψ`.
-/
