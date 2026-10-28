-- Prove2me | solution 1 for D1Bound5.signed_root_matrix_adjugate_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:51:39.794792+00:00
-- url     : https://prove2.me/submissions/7634f2c8-01a8-4ba3-b16f-065085106515

import Lean.Util.CollectAxioms
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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_normalizedRootError_diag
import Theorems.Thm_D1Bound5_symmetric_zero_four_adjugate_norm_lt

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- Transfer the adjugate bound to a simultaneously signed root matrix.
All entries and signs still live in the original commutative ring. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))).adjugate‖ <
        productFourH * productFourS^2 := by
  let fa : Fin 4 → ℂ := fun i => f (a i)
  let fS : Matrix (Fin 4) (Fin 4) ℂ := fun i j => f (S i j)
  let F := normalizedRootError fa u fS
  have hFdiag : ∀ i, F i i = 0 := by
    intro i
    exact normalizedRootError_diag fa u fS hu
      (fun j => congrArg f (hdiag j)) i
  have hFsymm : ∀ i j, F i j = F j i := by
    intro i j
    change u i * f (S i j) * u j - f (a i) * f (a j) =
      u j * f (S j i) * u i - f (a j) * f (a i)
    rw [hsymm i j]
    ring
  have hFsmall : ∀ i j, i ≠ j →
      ‖F i j - (1/2 : ℂ)‖ < (128/8649 : ℝ) := by
    intro i j hij
    change ‖(u i * f (S i j) * u j - f (a i) * f (a j)) -
      (1/2 : ℂ)‖ < (128/8649 : ℝ)
    exact (hgood i j hij).2
  exact symmetric_zero_four_adjugate_norm_lt F hFdiag hFsymm hFsmall



end D1Bound5
end
