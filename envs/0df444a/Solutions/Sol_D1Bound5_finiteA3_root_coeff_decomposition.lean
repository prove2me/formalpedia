-- Prove2me | solution 1 for D1Bound5.finiteA3_root_coeff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:59.934852+00:00
-- url     : https://prove2.me/submissions/4fad04e6-7cf5-40ff-a9a1-159a3c75e364

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
namespace D1Bound5











theorem _root_.solution {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteA3Left x y c i,finiteA3Right x y c i] j =
      ∑ ell : Fin 4, finiteA3RootCoeff x y i j ell*c^(ell : ℕ) := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [finiteA3Left,finiteA3Right,finiteA3RootCoeff,
      finiteA3Coeff0,finiteA3Coeff1,finiteA3Coeff2,finiteA3Coeff3,finiteHomogeneousTwo,Fin.sum_univ_succ]
    <;> ring











end D1Bound5
end
