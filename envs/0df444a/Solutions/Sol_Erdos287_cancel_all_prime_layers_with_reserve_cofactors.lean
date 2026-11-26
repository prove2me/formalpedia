-- Prove2me | solution 1 for Erdos287.cancel_all_prime_layers_with_reserve_cofactors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:09:22.994202+00:00
-- url     : https://prove2.me/submissions/f760c904-36ea-43c2-9b60-76067d539369

import Mathlib
import Theorems.Thm_Erdos287_cancel_prime_layer_with_reserve_cofactors

open Finset

set_option autoImplicit false

/-- Starting with the highest valuation, clear every power of `p` by
adding from the reserves, using at most `p - 1` cofactors at each level. -/
theorem solution (p E L : ℕ) (A : ℤ) (S : ℕ → Finset ℕ)
    (hp : p.Prime) (hL : ¬ p ∣ L)
    (hcard : ∀ a ∈ Finset.Icc 1 E, p - 1 ≤ (S a).card)
    (hcof : ∀ a ∈ Finset.Icc 1 E, ∀ c ∈ S a, 0 < c ∧ c ∣ L) :
    ∃ T : ℕ → Finset ℕ,
      (∀ a, T a ⊆ S a ∧ (T a).card ≤ p - 1) ∧
      ∃ K : ℤ,
        (A : ℚ) / ((p : ℚ) ^ E * L) +
          (∑ a ∈ Finset.Icc 1 E, ∑ c ∈ T a, (1 : ℚ) / ((p : ℚ) ^ a * c)) =
          (K : ℚ) / L := by
  induction E generalizing A with
  | zero =>
      refine ⟨fun _ => ∅, fun a => ⟨empty_subset _, by simp⟩, A, ?_⟩
      simp
  | succ E ih =>
      have htop : E + 1 ∈ Icc 1 (E + 1) := mem_Icc.mpr (by omega)
      have hlevels : Icc 1 E ⊆ Icc 1 (E + 1) := by
        intro a ha
        exact mem_Icc.mpr ⟨(mem_Icc.mp ha).1, (mem_Icc.mp ha).2.trans (Nat.le_succ E)⟩
      obtain ⟨U, hUS, hUcard, B, hB⟩ :=
        Erdos287.cancel_prime_layer_with_reserve_cofactors p (E + 1) L A (S (E + 1))
          hp (by omega) hL (hcard _ htop) (hcof _ htop)
      simp only [Nat.add_sub_cancel] at hB
      obtain ⟨T, hT, K, hK⟩ := ih B (fun a ha => hcard a (hlevels ha))
        (fun a ha => hcof a (hlevels ha))
      let R (a : ℕ) := if a = E + 1 then U else T a
      refine ⟨R, ?_, K, ?_⟩
      · intro a
        by_cases ha : a = E + 1
        · subst a
          simpa [R] using And.intro hUS hUcard
        · simpa [R, ha] using hT a
      have hnew : Icc 1 (E + 1) = insert (E + 1) (Icc 1 E) := by
        ext a
        simp only [mem_Icc, mem_insert]
        omega
      have hnot : E + 1 ∉ Icc 1 E := by simp
      rw [hnew, sum_insert hnot]
      have hsum :
          (∑ a ∈ Icc 1 E, ∑ c ∈ R a, (1 : ℚ) / ((p : ℚ) ^ a * c)) =
            ∑ a ∈ Icc 1 E, ∑ c ∈ T a, (1 : ℚ) / ((p : ℚ) ^ a * c) := by
        apply sum_congr rfl
        intro a ha
        have hle := (mem_Icc.mp ha).2
        simp [R, show a ≠ E + 1 by omega]
      rw [hsum, show R (E + 1) = U by simp [R], ← add_assoc, hB, hK]

