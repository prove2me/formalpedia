-- Prove2me | solution 1 for BookProof.AbelianDiagonal.diagonalStarAlgHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:38:54.68324+00:00
-- url     : https://prove2.me/submissions/463128f9-27aa-4ecc-ae54-cc17e38c2ee4

import Mathlib
import Definitions.Def_ChapterAbelianDiagonal

open Matrix BookProof.AbelianDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by
  intro d e h
  -- `diagonalStarAlgHom` is the star-algebra map whose underlying function is `Matrix.diagonal`
  have hd : Matrix.diagonal d = Matrix.diagonal e := by
    simpa [diagonalStarAlgHom] using h
  ext i
  have := congrArg (fun M : Matrix n n ℂ => M i i) hd
  simpa using this
