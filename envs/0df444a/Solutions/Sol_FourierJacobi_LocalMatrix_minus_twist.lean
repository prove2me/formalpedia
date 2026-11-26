-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.minus_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:48.467264+00:00
-- url     : https://prove2.me/submissions/c6ef9a87-2faa-40fc-8f22-65e75773092b

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
    E (-1) * g a x y z * E (-1) = D a * N (-x) y (-z) := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ])
end FourierJacobi.LocalMatrix
