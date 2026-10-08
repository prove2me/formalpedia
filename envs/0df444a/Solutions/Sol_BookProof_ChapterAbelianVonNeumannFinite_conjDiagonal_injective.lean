-- Prove2me | solution 1 for BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:19.297849+00:00
-- url     : https://prove2.me/submissions/c23c2b38-33e9-4dd0-985c-486682f03319

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

namespace BookProof.ChapterAbelianVonNeumannFinite
@[simp] theorem diagonalStarAlgHom_apply (d : n → ℂ) :
    (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) d = diagonal d := rfl

theorem diagonalStarAlgHom_injective :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by
  intro d d' h
  funext i
  have := congrFun (congrFun h i) i
  simpa using this

@[simp] theorem conjDiagonal_apply (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
    conjDiagonal U d = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) (diagonal d) := rfl
end BookProof.ChapterAbelianVonNeumannFinite

theorem solution (U : Matrix.unitaryGroup n ℂ) :
    Function.Injective (conjDiagonal U) := by
  intro d d' h
  refine diagonalStarAlgHom_injective ?_
  simpa [conjDiagonal_apply] using
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U).injective h

#print axioms solution

