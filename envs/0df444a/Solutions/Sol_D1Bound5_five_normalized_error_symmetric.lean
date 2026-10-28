-- Prove2me | solution 1 for D1Bound5.five_normalized_error_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:30.49319+00:00
-- url     : https://prove2.me/submissions/8b89a657-b9bf-4c28-8951-3da968a7db16

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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions

section
open Matrix

namespace D1Bound5



/-- Symmetry survives the square-root normalization, with no nonzero
hypotheses on tuple entries or auxiliary roots. -/
theorem _root_.solution
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hsym : Mᵀ = M) :
    (normalizedRootError t u M)ᵀ = normalizedRootError t u M := by
  ext i j
  change u j * M j i * u i - t j * t i =
    u i * M i j * u j - t i * t j
  have h := congrArg
    (fun N : Matrix (Fin 5) (Fin 5) ℂ => N i j) hsym
  change M j i = M i j at h
  rw [h]
  ring



end D1Bound5
end
