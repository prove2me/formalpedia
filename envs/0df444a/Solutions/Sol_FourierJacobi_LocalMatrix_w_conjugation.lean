-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.w_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:09.528604+00:00
-- url     : https://prove2.me/submissions/b10f3bf7-fd5f-4f91-ba70-95aaeb5f7c19

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
theorem _root_.solution (a x y z : K) :
    wInv * g a x y z * w =
      !![1, -y, 0, z; 0, a⁻¹, 0, 0; 0, -a * x, a, a * y; 0, 0, 0, 1] := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ])
end FourierJacobi.LocalMatrix
