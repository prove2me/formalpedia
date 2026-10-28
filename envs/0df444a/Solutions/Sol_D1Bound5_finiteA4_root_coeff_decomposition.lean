-- Prove2me | solution 1 for D1Bound5.finiteA4_root_coeff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:04.658172+00:00
-- url     : https://prove2.me/submissions/7e5f20e1-cb68-4634-a3e4-5d8d513c1663

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
namespace D1Bound5













theorem _root_.solution {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteA4Left x y c i,finiteA4Right x y c i] j =
      ∑ ell : Fin 5, finiteA4RootCoeff x y i j ell*c^(ell : ℕ) := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [finiteA4Left,finiteA4Right,finiteA4RootCoeff,
      finiteA4Coeff0,finiteA4Coeff1,finiteA4Coeff2,finiteA4Coeff3,finiteA4Coeff4,finiteHomogeneousTwo,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    <;> ring













end D1Bound5
end
