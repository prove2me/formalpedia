-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.S_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:48:23.076987+00:00
-- url     : https://prove2.me/submissions/1be8e9a0-2cab-4b9e-ba00-f8777df9c127

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.S_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
open BookProof.ChapterWignerSymmetry

theorem solution(hS : WignerCoord S o) {v : ι → ℂ} {k : ι} (h : v k = 0) : S v k = 0 := by
  have := hS.coord_norm v k
  rw [h, norm_zero] at this
  exact norm_eq_zero.mp this
