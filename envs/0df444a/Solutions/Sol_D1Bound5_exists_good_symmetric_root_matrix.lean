-- Prove2me | solution 1 for D1Bound5.exists_good_symmetric_root_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:31.61689+00:00
-- url     : https://prove2.me/submissions/a94b7c68-e16f-4cbe-a9cd-04523833ad29

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
import Theorems.Thm_D1Bound5_signed_entry_good_or_neg

section
namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- Interchanging endpoints preserves the two error inequalities. -/
theorem signed_entry_good_swap {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (h : SignedEntryGood f a b u v r) :
    SignedEntryGood f b a v u r := by
  unfold SignedEntryGood at h ⊢
  have heq : v * f r * u = u * f r * v := by ring
  rw [heq, mul_comm (f b) (f a)]
  exact h

/-- The signs can be chosen for all six unordered off-diagonal positions
of a symmetric four-by-four integral root matrix simultaneously. The
chosen matrix remains symmetric and its entries remain in the original ring.
No nonzero-root or distinct-modulus assumptions are used. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (M : Matrix (Fin 4) (Fin 4) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hlarge : ∀ i j, i ≠ j → 9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ S : Matrix (Fin 4) (Fin 4) R,
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → SignedEntryGood f (a i) (a j) (u i) (u j) (S i j)) := by
  classical
  let q : Fin 4 → Fin 4 → R := fun i j =>
    if SignedEntryGood f (a i) (a j) (u i) (u j) (M i j) then
      M i j else -M i j
  have hqsign (i j : Fin 4) : q i j = M i j ∨ q i j = -M i j := by
    dsimp [q]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hqgood (i j : Fin 4) (hij : i ≠ j) :
      SignedEntryGood f (a i) (a j) (u i) (u j) (q i j) := by
    dsimp [q]
    split_ifs with h
    · exact h
    · rcases signed_entry_good_or_neg f (a i) (a j) (M i j)
        (u i) (u j) (hu i) (hu j) (hroot i j hij)
        (hlarge i j hij) with hp | hn
      · exact False.elim (h hp)
      · exact hn
  let S : Matrix (Fin 4) (Fin 4) R := fun i j =>
    if i = j then a i else q (min i j) (max i j)
  have hSdiag (i : Fin 4) : S i i = a i := by simp [S]
  have hSsym (i j : Fin 4) : S i j = S j i := by
    by_cases h : i = j
    · subst j
      rfl
    · simp [S, h, Ne.symm h, min_comm, max_comm]
  have hSsign (i j : Fin 4) (hij : i ≠ j) :
      S i j = M i j ∨ S i j = -M i j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simpa [S, hij, min_eq_left hlt.le, max_eq_right hlt.le] using hqsign i j
    · exact False.elim (hij heq)
    · have hq := hqsign j i
      simpa [S, hij, min_eq_right hgt.le, max_eq_left hgt.le, hsymm j i] using hq
  have hSroot (i j : Fin 4) (hij : i ≠ j) :
      (S i j)^2 = a i * a j + 1 := by
    rcases hSsign i j hij with h | h
    · rw [h]
      exact hroot i j hij
    · rw [h]
      simpa only [neg_sq] using hroot i j hij
  have hSgood (i j : Fin 4) (hij : i ≠ j) :
      SignedEntryGood f (a i) (a j) (u i) (u j) (S i j) := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simpa [S, hij, min_eq_left hlt.le, max_eq_right hlt.le] using
        hqgood i j hij
    · exact False.elim (hij heq)
    · have h := signed_entry_good_swap f (a j) (a i) (q j i) (u j) (u i)
        (hqgood j i hij.symm)
      simpa [S, hij, min_eq_right hgt.le, max_eq_left hgt.le] using h
  exact ⟨S, hSdiag, hSsym, hSsign, hSroot, hSgood⟩

end D1Bound5

namespace D1Bound5



end D1Bound5
end
