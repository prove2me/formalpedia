-- Prove2me | solution 1 for D1Bound5.five_prefix_det_upper_of_mixed_signed_entries
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:25.202268+00:00
-- url     : https://prove2.me/submissions/10bf6f4c-0a3f-4039-be38-233137b4a4f8

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
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_mixed_signed_root_det_upper_33_128

section
open Matrix

namespace D1Bound5



/-- The exact four-entry determinant estimate inside a full five-entry
integral root matrix, conditional only on the signed first-four entries.
No condition on the fifth row or column is used here. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hsymm : ∀ i j, S i j = S j i)
    (hgood : ∀ i j : Fin 4, i ≠ j →
      MixedSignedEntryGood f
        (fun k => a (Fin.castAdd 1 k)) (fun k => u (Fin.castAdd 1 k))
        i j (S (Fin.castAdd 1 i) (Fin.castAdd 1 j))) :
    ‖(fivePrefixError (normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j)))).det‖ < (33/128 : ℝ) := by
  let a4 : Fin 4 → R := fun i => a (Fin.castAdd 1 i)
  let u4 : Fin 4 → ℂ := fun i => u (Fin.castAdd 1 i)
  let S4 : Matrix (Fin 4) (Fin 4) R :=
    fun i j => S (Fin.castAdd 1 i) (Fin.castAdd 1 j)
  have heq : fivePrefixError (normalizedRootError (fun i => f (a i)) u
      (fun i j => f (S i j))) =
    normalizedRootError (fun i => f (a4 i)) u4 (fun i j => f (S4 i j)) := by
    ext i j
    rfl
  rw [heq]
  exact mixed_signed_root_det_upper_33_128 f a4 u4 S4
    (fun i => hu (Fin.castAdd 1 i))
    (fun i => hdiag (Fin.castAdd 1 i))
    (fun i j => hsymm (Fin.castAdd 1 i) (Fin.castAdd 1 j))
    (fun i j hij => hgood i j hij)

end D1Bound5
end
