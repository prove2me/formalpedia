-- Prove2me | solution 1 for D1Bound5.referenceReflection_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:21.089372+00:00
-- url     : https://prove2.me/submissions/8ab77c9c-dcfa-4eca-8e6f-66eeb4b86e0c

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
    referenceReflectionᴴ = referenceReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [referenceReflection,
      Matrix.conjTranspose_apply]















end D1Bound5
end
