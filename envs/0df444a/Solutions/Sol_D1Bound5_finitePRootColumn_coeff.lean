-- Prove2me | solution 1 for D1Bound5.finitePRootColumn_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:52.813295+00:00
-- url     : https://prove2.me/submissions/bc4c2184-8a88-445c-9b2b-0f856e6c25c1

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
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three











theorem _root_.solution {R : Type*} [CommRing R]
    (a b s c : R) (i : Fin 4) (j : Fin 3) :
    finitePRootColumn a b s c i j = finitePRootCoeff a b s i 0 j +
      finitePRootCoeff a b s i 1 j*c+finitePRootCoeff a b s i 2 j*c^2 := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [finitePRootColumn, finitePDividedMatrix, finitePRootCoeff,
      finitePRootTerms, finitePTermValue, finitePRLeft, finitePRRight,
      finitePTLeft, finitePTRight, finitePairQuadratic, finitePRLeftCoeff,
      finitePRRightCoeff, finitePTLeftCoeff, finitePTRightCoeff, Fin.sum_univ_succ]
    <;> ring

















end D1Bound5
end
