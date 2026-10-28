-- Prove2me | solution 1 for D1Bound5.signed_root_matrix_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:22:36.158892+00:00
-- url     : https://prove2.me/submissions/d34aa9c7-7bc0-4a09-b5dd-58dad250d573

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_four_zero_diagonal_operator_norm_lt
import Theorems.Thm_D1Bound5_normalizedRootError_diag

section
open scoped Matrix.Norms.L2Operator

namespace D1Bound5



/-- The six signed entry bounds imply the strict Euclidean operator-norm
estimate for the full normalized correction matrix. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j →
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) :
    ‖normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j)) - halfOffDiagonal‖ <
      3 * (128/8649 : ℝ) := by
  let fa : Fin 4 → ℂ := fun i => f (a i)
  let fS : Matrix (Fin 4) (Fin 4) ℂ := fun i j => f (S i j)
  let F := normalizedRootError fa u fS
  let E := F - halfOffDiagonal
  have hd (i : Fin 4) : fS i i = fa i := congrArg f (hdiag i)
  have hF (i : Fin 4) : F i i = 0 :=
    normalizedRootError_diag fa u fS hu hd i
  have hEdiag (i : Fin 4) : E i i = 0 := by
    change F i i - halfOffDiagonal i i = 0
    simp [hF i, halfOffDiagonal]
  have hEoff (i j : Fin 4) (hij : i ≠ j) :
      ‖E i j‖ < (128/8649 : ℝ) := by
    have hg := (hgood i j hij).2
    change ‖u i * f (S i j) * u j - f (a i) * f (a j) - (1/2 : ℂ)‖ <
      (128/8649 : ℝ) at hg
    have hE : E i j =
        u i * f (S i j) * u j - f (a i) * f (a j) - (1/2 : ℂ) := by
      simp [E, F, fa, fS, normalizedRootError, scaledRootMatrix,
        halfOffDiagonal, hij]
    rw [hE]
    exact hg
  exact four_zero_diagonal_operator_norm_lt E (128/8649 : ℝ)
    (by norm_num) hEdiag hEoff



end D1Bound5
end
