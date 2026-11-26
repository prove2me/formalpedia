-- Prove2me | solution 1 for Erdos266.det_latticeMatrix_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:36.722039+00:00
-- url     : https://prove2.me/submissions/408b40dd-610a-438a-9a82-53c7fefdde0a

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix
namespace Erdos266
theorem _root_.solution (d : ℕ) : (latticeMatrix d).det ≠ 0 := by
  classical
  have hW : latticeMatrix d
      = ((Matrix.vandermonde fun i : Fin d => ((i : ℤ) + 1)).transpose).submatrix
          Fin.revPerm id := by
    ext i j
    simp only [latticeMatrix, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Matrix.vandermonde, Fin.revPerm_apply, id_eq,
      Matrix.of_apply, Fin.val_rev]
    congr 1
    omega
  rw [hW, Matrix.det_permute]
  refine mul_ne_zero (Units.ne_zero _) ?_
  rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 := hab
  have : (a : ℕ) = b := by omega
  exact Fin.ext this
end Erdos266
