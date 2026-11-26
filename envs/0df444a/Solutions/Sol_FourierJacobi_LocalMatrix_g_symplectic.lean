-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.g_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:32.75315+00:00
-- url     : https://prove2.me/submissions/3b838024-c692-4749-bbcf-4f335d7fb021

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
theorem _root_.solution (a x y z : K) (ha : a ≠ 0) :
    (g a x y z).transpose * J * g a x y z = J := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> field_simp <;> ring
end FourierJacobi.LocalMatrix
