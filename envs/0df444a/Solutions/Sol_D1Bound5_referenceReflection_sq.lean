-- Prove2me | solution 1 for D1Bound5.referenceReflection_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:07.039985+00:00
-- url     : https://prove2.me/submissions/c3871884-f863-4bfc-ac30-5bb1651c7c5d

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ReferenceInverseNorm_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



theorem _root_.solution :
    referenceReflection * referenceReflection = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [referenceReflection, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> norm_num

















end D1Bound5
end
