-- Prove2me | solution 1 for Eden.charpoly_diagonalLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:21.278664+00:00
-- url     : https://prove2.me/submissions/0310b6ce-ccee-489c-a0ec-3ca6c5511428

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
import Theorems.Thm_Eden_toMatrix_diagonalLinear

set_option autoImplicit true
noncomputable section
open Polynomial
open Eden
namespace Eden
theorem _root_.solution (d : PhaseSpace) :
    (diagonalLinear d).charpoly = ∏ i : Fin 5, (X - C (d i)) := by
  rw [← (diagonalLinear d).charpoly_toMatrix (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis,
    toMatrix_diagonalLinear, Matrix.charpoly_diagonal]
end Eden
