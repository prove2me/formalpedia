-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.submatrix_mul_castLE_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:51.69389+00:00
-- url     : https://prove2.me/submissions/c6608e79-4811-4b89-b0eb-67f81431128f

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
    (Lo : Matrix (Fin N) (Fin N) R) (X : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hLo : ∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → Lo i j = 0) :
    (Lo * X).submatrix (Fin.castLE hl) g =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) g := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
  · intro k hk
    have : l ≤ (k : ℕ) := by
      by_contra hlt
      exact hk ⟨⟨k, by omega⟩, by ext; simp⟩
    rw [hLo _ _ (by simp) this, zero_mul]
  · intro k; rfl
end Formalism.HermitianLatticeCounting.P
