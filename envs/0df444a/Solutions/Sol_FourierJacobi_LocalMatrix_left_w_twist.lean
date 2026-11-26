-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.left_w_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:08.60183+00:00
-- url     : https://prove2.me/submissions/ea592b2c-46d9-49a5-8746-97caa828da07

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
theorem _root_.solution (a x y z p : K) (ha : a ≠ 0) (hp : p ≠ 0) :
    E p⁻¹ * wInv * g a x y z * E p =
      wInv * D (a / p) * N (p * x) y (z / p) := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp
end FourierJacobi.LocalMatrix
