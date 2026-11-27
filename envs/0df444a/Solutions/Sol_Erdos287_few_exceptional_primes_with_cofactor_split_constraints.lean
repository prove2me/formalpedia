-- Prove2me | solution 1 for Erdos287.few_exceptional_primes_with_cofactor_split_constraints
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:42:57.132367+00:00
-- url     : https://prove2.me/submissions/9e4fb692-1903-4f6c-8388-689d9045b32e

import Mathlib
import Theorems.Thm_Erdos287_cofactor_split_pattern_count
import Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets

open Finset

set_option autoImplicit false

/-- A fixed endpoint and disjoint split constraints reduce the number
of large primes that can pass a cofactor residue test. -/
theorem solution (U I P : Finset ℕ) (c L Y K : ℕ) (A : ℕ → Finset ℕ)
    (hc : c ∈ U) (hL : 0 < L) (hY : 2 ≤ Y) (hU : ∀ a ∈ U, 0 < a ∧ a ∣ L)
    (hA : ∀ i ∈ I, A i ⊆ U.erase c)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j))
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p) (hbound : U.card * L < Y ^ (K + 1))
    (hpass : ∀ p ∈ P, ∃ T ⊆ U, c ∈ T ∧ (∀ i ∈ I, (T ∩ A i).Nonempty) ∧
      p ∣ ∑ a ∈ T, L / a) :
    P.card ≤ (2 ^ (U.card - (1 + ∑ i ∈ I, (A i).card)) *
      ∏ i ∈ I, (2 ^ (A i).card - 1)) * K := by
  classical
  let F := U.powerset.filter (fun T => c ∈ T ∧ ∀ i ∈ I, (T ∩ A i).Nonempty)
  have hF (T : Finset ℕ) (hT : T ∈ F) : T ⊆ U ∧ T.Nonempty := by
    obtain ⟨hTU, hcT, _⟩ := mem_filter.mp hT
    exact ⟨mem_powerset.mp hTU, ⟨c, hcT⟩⟩
  have hExc (p : ℕ) (hp : p ∈ P) : ∃ T ∈ F, p ∣ ∑ a ∈ T, L / a := by
    obtain ⟨T, hTU, hcT, hhit, hpT⟩ := hpass p hp
    exact ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hTU, hcT, hhit⟩, hpT⟩
  have hCount := Erdos287.cofactor_split_pattern_count U I c A hc hA hdisj
  exact (Erdos287.few_exceptional_primes_for_cofactor_subsets U P F L Y K
    hL hY hU hF hP hbound hExc).trans (Nat.mul_le_mul_right K hCount)

