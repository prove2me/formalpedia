-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.right_w_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:49.358175+00:00
-- url     : https://prove2.me/submissions/9ac7ea3f-c234-48e3-8a2c-71461b6f0a70

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
    E p⁻¹ * g a x y z * w * E p =
      D (a * p) * N (x / p) (y / p) (z / p) * w := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp
end FourierJacobi.LocalMatrix
