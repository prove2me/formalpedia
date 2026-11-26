-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.heisenberg_rearrange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:36.860244+00:00
-- url     : https://prove2.me/submissions/8bebf26f-51f5-4c7f-b82d-7ca5eb9f51c5

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
theorem _root_.solution (y z u t : K) :
    YZ y z * X u * N (-t) 0 0 =
      N (-t) 0 0 * YZ (y - t * u) (z - t * u ^ 2) * X u := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]) <;> ring
end FourierJacobi.LocalMatrix
