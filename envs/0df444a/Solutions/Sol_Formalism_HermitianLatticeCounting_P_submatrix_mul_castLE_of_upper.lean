-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.300279+00:00
-- url     : https://prove2.me/submissions/d06b7b6a-1819-44ae-87c9-f8174183c442

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] {N l : ℕ} {α : Type*} (hl : l ≤ N)
    (X : Matrix (Fin N) (Fin N) R) (Up : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hUp : ∀ i j : Fin N, l ≤ (i : ℕ) → (j : ℕ) < l → Up i j = 0) :
    (X * Up).submatrix g (Fin.castLE hl) =
      X.submatrix g (Fin.castLE hl) * Up.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
  · intro k hk
    have : l ≤ (k : ℕ) := by
      by_contra hlt
      exact hk ⟨⟨k, by omega⟩, by ext; simp⟩
    rw [hUp _ _ this (by simp), mul_zero]
  · intro k; rfl
end Formalism.HermitianLatticeCounting.P
