-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.remove_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:38.492805+00:00
-- url     : https://prove2.me/submissions/bea62333-afa1-4bff-b2bd-92cb57a2d985

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
theorem _root_.solution (a x y z t r : K) (ha : a ≠ 0) :
    N t 0 0 * X (-r) * g a x y z =
      X (-r) * D a * N (x + t / a ^ 2) (y + r * t / a) (z + r ^ 2 * t) := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp <;> ring
end FourierJacobi.LocalMatrix
