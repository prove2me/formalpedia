-- Prove2me | solution 1 for FourierJacobi.LocalMatrix.all_two_by_two_minors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:29.578453+00:00
-- url     : https://prove2.me/submissions/79357383-08d6-40ee-8035-79eb8ce9e176

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
    secondCompound (g a x y z) =
      !![a, a * x, a * y, -a * y, -a * z, a * (y ^ 2 - x * z);
         0, a⁻¹, 0, 0, 0, -z / a;
         0, 0, 1, 0, 0, y;
         0, 0, 0, 1, 0, -y;
         0, 0, 0, 0, a, a * x;
         0, 0, 0, 0, 0, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondCompound, indexPairs, g, D, N, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> field_simp
end FourierJacobi.LocalMatrix
