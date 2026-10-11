-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.map_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:34:54.458874+00:00
-- url     : https://prove2.me/submissions/0c906c8e-c3e4-49e6-8d79-8809d6da5e09

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.map_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}
open BookProof.ChapterWignerSymmetry

theorem solution(hT : IsWignerSymmetry T) : T 0 = 0 := by
  exact norm_eq_zero.mp (by simpa using BookProof.ChapterWignerSymmetry.norm_map hT 0)
