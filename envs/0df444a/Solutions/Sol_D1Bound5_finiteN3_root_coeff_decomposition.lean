-- Prove2me | solution 1 for D1Bound5.finiteN3_root_coeff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:11.104183+00:00
-- url     : https://prove2.me/submissions/6db78bda-0d02-495b-883c-747612b2fcdf

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
namespace D1Bound5












/-- Exact coefficient vectors, checked against the actual N3 matrix. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN3Left x y c i,finiteN3Right x y c i] j =
      finiteHomogeneousTwo 4 (finiteN3Coeff0 i j) x y +
      finiteHomogeneousTwo 5 (finiteN3Coeff1 i j) x y*c +
      finiteHomogeneousTwo 6 (finiteN3Coeff2 i j) x y*c^2 +
      finiteHomogeneousTwo 7 (finiteN3Coeff3 i j) x y*c^3 := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [finiteN3Left,finiteN3Right,finiteN3Coeff0,finiteN3Coeff1,
      finiteN3Coeff2,finiteN3Coeff3,finiteHomogeneousTwo,Fin.sum_univ_succ]
    <;> ring









end D1Bound5
end
