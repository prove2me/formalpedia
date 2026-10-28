-- Prove2me | solution 1 for D1Bound5.five_prefix_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:25.792208+00:00
-- url     : https://prove2.me/submissions/151e3158-1863-467a-ab31-dcd185d05e56

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
open Matrix

namespace D1Bound5

/-- A symmetric five-by-five matrix has a symmetric four-by-four leading block. -/
theorem _root_.solution
    (E : Matrix (Fin 5) (Fin 5) ℂ) (hsym : Eᵀ = E) :
    (fivePrefixError E)ᵀ = fivePrefixError E := by
  ext i j
  change E (Fin.castAdd 1 j) (Fin.castAdd 1 i) =
    E (Fin.castAdd 1 i) (Fin.castAdd 1 j)
  have h := congrArg
    (fun N : Matrix (Fin 5) (Fin 5) ℂ =>
      N (Fin.castAdd 1 i) (Fin.castAdd 1 j)) hsym
  simpa only [Matrix.transpose_apply] using h





end D1Bound5
end
