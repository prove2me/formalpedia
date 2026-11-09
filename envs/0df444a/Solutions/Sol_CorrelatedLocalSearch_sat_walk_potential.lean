-- Prove2me | solution 1 for CorrelatedLocalSearch.sat_walk_potential
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:03:43.838856+00:00
-- url     : https://prove2.me/submissions/db6b222f-244a-4cc0-b89c-181e557b871f

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau

set_option autoImplicit false

namespace Aux_CLSwalk
open CorrelatedLocalSearch

theorem flip_self {n : ℕ} (x : Fin n → Bool) (v : Fin n) : flipVar x v v = !x v := by
  simp [flipVar]

theorem flip_ne {n : ℕ} (x : Fin n → Bool) (v i : Fin n) (h : i ≠ v) : flipVar x v i = x i := by
  simp [flipVar, Function.update_of_ne h]

theorem flip_dec {n : ℕ} (x xs : Fin n → Bool) (v : Fin n) (h : x v ≠ xs v) :
    hammingDist (flipVar x v) xs + 1 = hammingDist x xs := by
  unfold hammingDist
  have hb : (!x v) = xs v := by
    cases hx : x v <;> cases hy : xs v <;> simp_all
  have hS : (Finset.univ.filter fun i => x i ≠ xs i) =
      insert v (Finset.univ.filter fun i => flipVar x v i ≠ xs i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hi : i = v
    · subst hi
      simp [h]
    · rw [flip_ne x v i hi]
      simp [hi]
  have hv : v ∉ (Finset.univ.filter fun i => flipVar x v i ≠ xs i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    rw [flip_self, hb]
  rw [hS, Finset.card_insert_of_notMem hv]

theorem flip_inc {n : ℕ} (x xs : Fin n → Bool) (v : Fin n) (h : x v = xs v) :
    hammingDist (flipVar x v) xs = hammingDist x xs + 1 := by
  unfold hammingDist
  have hS : (Finset.univ.filter fun i => flipVar x v i ≠ xs i) =
      insert v (Finset.univ.filter fun i => x i ≠ xs i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hi : i = v
    · subst hi
      rw [flip_self, ← h]
      cases hb : x i <;> simp
    · rw [flip_ne x v i hi]
      simp [hi]
  have hv : v ∉ (Finset.univ.filter fun i => x i ≠ xs i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact h
  rw [hS, Finset.card_insert_of_notMem hv]

end Aux_CLSwalk

open CorrelatedLocalSearch in
theorem solution (k r n : ℕ) (hk : k < 2 * r) (hr : r < k)
    (Φ : List (Clause k n)) (xs : Fin n → Bool) (hxs : IsStrongWitness r Φ xs) :
    (∀ C ∈ Φ, ∀ x : Fin n → Bool, C.Violated x →
        r ≤ Set.ncard {i : Fin k |
          hammingDist (flipVar x (C.lit i).1) xs + 1 = hammingDist x xs}) ∧
      (∀ (x : Fin n → Bool) (v : Fin n),
        hammingDist (flipVar x v) xs = hammingDist x xs + 1 ∨
          hammingDist (flipVar x v) xs + 1 = hammingDist x xs) ∧
      (∀ x : Fin n → Bool, hammingDist x xs = 0 → Satisfies Φ x) := by
  refine ⟨fun C hC x hviol => ?_, fun x v => ?_, fun x hx => ?_⟩
  · refine (hxs C hC).trans (Set.ncard_le_ncard ?_)
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    apply Aux_CLSwalk.flip_dec
    intro heq
    exact hviol i (heq.trans hi)
  · by_cases h : x v = xs v
    · exact Or.inl (Aux_CLSwalk.flip_inc x xs v h)
    · exact Or.inr (Aux_CLSwalk.flip_dec x xs v h)
  · rw [hammingDist_eq_zero] at hx
    rw [hx]
    intro C hC hviol
    have hpos : 0 < Set.ncard {i : Fin k | xs (C.lit i).1 = (C.lit i).2} := by
      have := hxs C hC
      omega
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    exact hviol i hi
