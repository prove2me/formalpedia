-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.w_remove_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:13.941177+00:00
-- url     : https://prove2.me/submissions/187b26f7-bb3c-4698-833e-935905bbd80a

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
theorem _root_.solution (a x y z r s : K) (ha : a ≠ 0) :
    YZ r 0 * wInv * N (-s) 0 0 * X (-r) * D a * N x y z * w =
      wInv * D a * N (x - s / a ^ 2) (y - r * s / a) (z - r ^ 2 * s) * w := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp <;> ring
end FourierJacobi.LocalMatrix
