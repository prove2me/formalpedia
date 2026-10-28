-- Prove2me | solution 1 for D1Bound5.finiteN2_root_coeff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:49.239886+00:00
-- url     : https://prove2.me/submissions/b48884bd-45ef-4db4-a2fb-28b47fb7f08f

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5







/-- Exact homogeneous decomposition of both divided root columns. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN2Left x y c i, finiteN2Right x y c i] j =
      finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) x y +
      finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) x y*c +
      finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) x y*c^2 := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [finiteN2Left, finiteN2Right, finiteN2Coeff0, finiteN2Coeff1,
      finiteN2Coeff2, finiteHomogeneousTwo, Fin.sum_univ_succ]
    <;> ring









end D1Bound5
end
