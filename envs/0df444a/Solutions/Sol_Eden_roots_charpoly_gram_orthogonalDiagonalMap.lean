-- Prove2me | solution 1 for Eden.roots_charpoly_gram_orthogonalDiagonalMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:19.339891+00:00
-- url     : https://prove2.me/submissions/2c4c7670-d46b-43de-b879-bf0cde663789

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
import Theorems.Thm_Eden_roots_charpoly_diagonalLinear
import Theorems.Thm_Eden_gram_orthogonalDiagonalMap

set_option autoImplicit true
noncomputable section
open Polynomial
open Eden
namespace Eden
theorem _root_.solution
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    ((orthogonalDiagonalMap U V d).adjoint ∘ₗ orthogonalDiagonalMap U V d).charpoly.roots =
      Finset.univ.val.map (fun i : Fin 5 => d i ^ 2) := by
  rw [gram_orthogonalDiagonalMap, LinearEquiv.charpoly_conj, roots_charpoly_diagonalLinear]
end Eden
