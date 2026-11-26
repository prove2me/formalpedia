-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.twist_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:47.405651+00:00
-- url     : https://prove2.me/submissions/0b4b0c05-d2dd-4d17-82d9-b83edefba644

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
theorem _root_.solution (a x y z p : K) (hp : p ≠ 0) :
    E p⁻¹ * g a x y z * E p = D a * N (p * x) y (z / p) := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp
end FourierJacobi.LocalMatrix
