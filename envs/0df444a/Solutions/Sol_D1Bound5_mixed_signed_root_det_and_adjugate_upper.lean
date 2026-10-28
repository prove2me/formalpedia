-- Prove2me | solution 1 for D1Bound5.mixed_signed_root_det_and_adjugate_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:28.352985+00:00
-- url     : https://prove2.me/submissions/a8e404ee-d431-45c7-9692-24c82a995a15

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_mixed_signed_root_adjugate_upper
import Theorems.Thm_D1Bound5_mixed_signed_root_det_upper

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



/-- Both analytic bounds simultaneously hold for a single integral
choice of signs, not separate existential matrices. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (S : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      MixedSignedEntryGood f a u i j (S i j)) :
    ‖(normalizedRootError (fun i => f (a i)) u
       (fun i j => f (S i j))).det‖ < (3/10 : ℝ) ∧
    ‖(normalizedRootError (fun i => f (a i)) u
       (fun i j => f (S i j))).adjugate‖ <
       (155/96 : ℝ)*(59/96)^2 := by
  exact ⟨mixed_signed_root_det_upper f a u S hu hdiag hsymm hgood,
    mixed_signed_root_adjugate_upper f a u S hu hdiag hsymm hgood⟩

end D1Bound5
end
