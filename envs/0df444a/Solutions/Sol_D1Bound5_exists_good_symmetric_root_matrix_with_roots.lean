-- Prove2me | solution 1 for D1Bound5.exists_good_symmetric_root_matrix_with_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:15.862205+00:00
-- url     : https://prove2.me/submissions/34af1bb5-277a-47e5-b784-3b0a77b94989

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_exists_good_symmetric_root_matrix

section
namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- Simultaneously choose complex square roots of the four diagonal
entries and integral signs of all six off-diagonal roots. The
normalization is uniform without selecting an analytic square-root branch. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (M : Matrix (Fin 4) (Fin 4) R)
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hlarge : ∀ i j, i ≠ j → 9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ (u : Fin 4 → ℂ) (S : Matrix (Fin 4) (Fin 4) R),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j →
        SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) := by
  classical
  have hr (i : Fin 4) : ∃ z : ℂ, z^2 = f (a i) :=
    IsAlgClosed.exists_pow_nat_eq (f (a i)) (by decide : 0 < 2)
  let u : Fin 4 → ℂ := fun i => Classical.choose (hr i)
  have hu (i : Fin 4) : (u i)^2 = f (a i) := Classical.choose_spec (hr i)
  obtain ⟨S, hd, hs, hsgn, hsq, hnear⟩ :=
    exists_good_symmetric_root_matrix f a u M hu hdiag hsymm hroot hlarge
  exact ⟨u, S, hu, hd, hs, hsgn, hsq, hnear⟩

end D1Bound5
end
