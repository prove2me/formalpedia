-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.w_mul_wInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:30.982832+00:00
-- url     : https://prove2.me/submissions/b6d3cac1-c6f6-41d0-aff4-801cb21fee4e

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_Matrices

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.LocalMatrix
open Matrix
variable {K : Type*} [Field K]
namespace FourierJacobi.LocalMatrix
theorem _root_.solution : (w : Matrix (Fin 4) (Fin 4) K) * wInv = 1 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ])
end FourierJacobi.LocalMatrix
