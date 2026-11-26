-- Prove2me | solution 1 for Erdos287.few_exceptional_primes_for_cofactor_subsets
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:00:57.903089+00:00
-- url     : https://prove2.me/submissions/cf144638-19c7-45b6-93e6-0ea0e8d9f521

import Mathlib

open Finset

set_option autoImplicit false

/-- Few large primes can divide any of the cleared numerators in a finite
family of nonempty admissible cofactor subsets. -/
theorem solution (U P : Finset ℕ) (F : Finset (Finset ℕ)) (L Y K : ℕ)
    (hL : 0 < L) (hY : 2 ≤ Y) (hU : ∀ n ∈ U, 0 < n ∧ n ∣ L)
    (hF : ∀ T ∈ F, T ⊆ U ∧ T.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p)
    (hbound : U.card * L < Y ^ (K + 1))
    (hexception : ∀ p ∈ P, ∃ T ∈ F, p ∣ ∑ n ∈ T, L / n) :
    P.card ≤ F.card * K := by
  let num (T : Finset ℕ) := ∑ n ∈ T, L / n
  let divs (T : Finset ℕ) := P.filter (fun p => p ∣ num T)
  have hcount (T : Finset ℕ) (hTF : T ∈ F) : (divs T).card ≤ K := by
    obtain ⟨hTU, ⟨n, hn⟩⟩ := hF T hTF
    have hnumpos : 0 < num T := by
      have ⟨hnpos, hnL⟩ := hU n (hTU hn)
      have hterm := Nat.div_pos (Nat.le_of_dvd hL hnL) hnpos
      exact hterm.trans_le (single_le_sum (f := fun n => L / n) (fun _ _ => Nat.zero_le _) hn)
    have hnumlt : num T < Y ^ (K + 1) := by
      apply lt_of_le_of_lt _ hbound
      calc
        num T ≤ ∑ _ ∈ T, L := sum_le_sum (fun n _ => Nat.div_le_self L n)
        _ = T.card * L := by simp
        _ ≤ U.card * L := Nat.mul_le_mul_right _ (card_le_card hTU)
    have hprod : (∏ p ∈ divs T, p) ∣ num T := by
      apply Int.natCast_dvd_natCast.mp
      rw [Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ (fun p hp => Int.natCast_dvd_natCast.mpr (mem_filter.mp hp).2)
      intro p hp q hq hpq
      exact Nat.isCoprime_iff_coprime.mpr
        ((Nat.coprime_primes (hP p (mem_filter.mp hp).1).1 (hP q (mem_filter.mp hq).1).1).mpr hpq)
    have hlo : Y ^ (divs T).card ≤ ∏ p ∈ divs T, p :=
      pow_card_le_prod _ _ _ (fun p hp => (hP p (mem_filter.mp hp).1).2)
    have hlt := hlo.trans_lt ((Nat.le_of_dvd hnumpos hprod).trans_lt hnumlt)
    exact Nat.lt_succ_iff.mp ((pow_lt_pow_iff_right₀ (show 1 < Y by omega)).mp hlt)
  have hcover : P ⊆ F.biUnion divs := by
    intro p hp
    obtain ⟨T, hTF, hq⟩ := hexception p hp
    exact mem_biUnion.mpr ⟨T, hTF, mem_filter.mpr ⟨hp, hq⟩⟩
  calc
    P.card ≤ (F.biUnion divs).card := card_le_card hcover
    _ ≤ ∑ T ∈ F, (divs T).card := card_biUnion_le
    _ ≤ ∑ _ ∈ F, K := sum_le_sum hcount
    _ = F.card * K := by simp

