-- Prove2me | solution 1 for D1Bound5.five_reindex_rankOne_plus_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:31.898457+00:00
-- url     : https://prove2.me/submissions/a2be576e-9e0a-49ae-b74b-f14b1825c71f

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
import Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
open Matrix

namespace D1Bound5









/-- The exact five-by-five block structure of a symmetric normalized root
matrix. No invertibility or nonzero tuple hypotheses are needed. -/
theorem _root_.solution
    (t : Fin 5 → ℂ) (E : Matrix (Fin 5) (Fin 5) ℂ)
    (hdiag : E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = 0)
    (hsym : Eᵀ = E) :
    Matrix.reindex (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5).symm
      (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5).symm
      (fun i j => t i * t j + E i j) =
      productFiveIntegratedBlock
        (fivePrefixError E) (fiveLastError E)
        (fivePrefixValues t) (fiveLastValue t) := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change t (Fin.castAdd 1 i) * t (Fin.castAdd 1 j) +
        E (Fin.castAdd 1 i) (Fin.castAdd 1 j) =
      fivePrefixError E i j + fivePrefixValues t i * fivePrefixValues t j
    simp [fivePrefixError, fivePrefixValues]
    ring
  · fin_cases j
    change t (Fin.castAdd 1 i) * t (Fin.natAdd 4 (0 : Fin 1)) +
        E (Fin.castAdd 1 i) (Fin.natAdd 4 (0 : Fin 1)) =
      fiveLastError E i + fiveLastValue t * fivePrefixValues t i
    simp [fiveLastError, fiveLastValue, fivePrefixValues]
    ring
  · fin_cases i
    have he : E (Fin.natAdd 4 (0 : Fin 1)) (Fin.castAdd 1 j) =
        E (Fin.castAdd 1 j) (Fin.natAdd 4 (0 : Fin 1)) := by
      have hh := congrArg
        (fun H : Matrix (Fin 5) (Fin 5) ℂ =>
          H (Fin.castAdd 1 j) (Fin.natAdd 4 (0 : Fin 1))) hsym
      simpa only [Matrix.transpose_apply] using hh
    change t (Fin.natAdd 4 (0 : Fin 1)) * t (Fin.castAdd 1 j) +
        E (Fin.natAdd 4 (0 : Fin 1)) (Fin.castAdd 1 j) =
      fiveLastError E j + fiveLastValue t * fivePrefixValues t j
    dsimp [fiveLastError, fiveLastValue, fivePrefixValues]
    change E (4 : Fin 5) (Fin.castAdd 1 j) = E (Fin.castAdd 1 j) 4 at he
    rw [he]
    ring
  · fin_cases i
    fin_cases j
    change t (Fin.natAdd 4 (0 : Fin 1)) *
      t (Fin.natAdd 4 (0 : Fin 1)) +
      E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) =
      (fiveLastValue t)^2
    rw [hdiag]
    simp [fiveLastValue, pow_two]





end D1Bound5
end
