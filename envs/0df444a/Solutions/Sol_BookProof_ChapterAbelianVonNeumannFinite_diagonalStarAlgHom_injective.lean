-- Prove2me | solution 1 for BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:58:35.857137+00:00
-- url     : https://prove2.me/submissions/9dcf4de5-86d4-424d-bb8c-0276d8bc6291

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

namespace BookProof.ChapterAbelianVonNeumannFinite
@[simp] theorem diagonalStarAlgHom_apply (d : n → ℂ) :
    (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) d = diagonal d := rfl
end BookProof.ChapterAbelianVonNeumannFinite

theorem solution :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by
  intro d d' h
  funext i
  have := congrFun (congrFun h i) i
  simpa using this

#print axioms solution
