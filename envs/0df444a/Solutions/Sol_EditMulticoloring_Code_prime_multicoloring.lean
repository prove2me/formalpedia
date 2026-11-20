-- Prove2me | solution 1 for EditMulticoloring.Code.prime_multicoloring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:39:42.004043+00:00
-- url     : https://prove2.me/submissions/d05063a9-66db-4102-8a76-36656b3d4ddd

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Graph

section
set_option autoImplicit false
namespace EditMulticoloring.Dev.PrimeMC
open EditMulticoloring.Code

lemma primeAt_prime (i : ℕ) : (primeAt i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

lemma primeAt_inj : Function.Injective primeAt :=
  Nat.nth_injective Nat.infinite_setOf_prime

lemma primeFactors_card_lt (n B : ℕ) (hn : n ≠ 0) (hB : n < 2 ^ B) :
    n.primeFactors.card ≤ B := by
  have h1 : ∏ p ∈ n.primeFactors, p ∣ n :=
    Finset.prod_primes_dvd (M₀ := ℕ) n (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors hp)
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
  have h3 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have : 2 ^ n.primeFactors.card < 2 ^ B := lt_of_le_of_lt (h3.trans h2) hB
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this |>.le

lemma bad_card (L B a b : ℕ) (hab : a ≠ b) (ha : a < 2 ^ B) (hb : b < 2 ^ B) :
    ((Finset.range L).filter (fun i => a % primeAt i = b % primeAt i)).card ≤ B := by
  have hne : ((a : ℤ) - b).natAbs ≠ 0 := by omega
  have hlt : ((a : ℤ) - b).natAbs < 2 ^ B := by omega
  refine le_trans ?_ (primeFactors_card_lt _ B hne hlt)
  apply Finset.card_le_card_of_injOn primeAt
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
    simp only [Finset.mem_coe, Nat.mem_primeFactors]
    refine ⟨primeAt_prime i, ?_, hne⟩
    have : (primeAt i : ℤ) ∣ (a : ℤ) - b := by
      have := (Nat.modEq_iff_dvd (n := primeAt i) (a := b) (b := a)).1 hi.2.symm
      exact this
    exact Int.natCast_dvd.mp this
  · intro i _ j _ h
    exact primeAt_inj h

lemma good_len {V : Type} [Fintype V] (G : SimpleGraph V) (r B : ℕ)
    (degree : ∀ v, (neighbors G v).card ≤ r) (f : V → ℕ) (range : ∀ v, f v < 2 ^ B)
    (proper : ∀ u v, G.Adj u v → f u ≠ f v) (L : ℕ) (v : V) :
    L - r * B ≤ (goodIndices G f L v).length := by
  classical
  have hsub : (Finset.range L).filter (fun i => ¬ Good G f v i) ⊆
      (neighbors G v).biUnion (fun u =>
        (Finset.range L).filter (fun i => f v % primeAt i = f u % primeAt i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Good, not_forall, not_not] at hi
    obtain ⟨hiL, u, hu, he⟩ := hi
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, neighbors,
      Finset.mem_univ, true_and]
    exact ⟨u, hu, hiL, he⟩
  have hcard : ((Finset.range L).filter (fun i => ¬ Good G f v i)).card ≤ r * B := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B ?_).trans ?_
    · intro u hu
      have hu' : G.Adj v u := by simpa [neighbors] using hu
      exact bad_card L B _ _ (proper v u hu') (range v) (range u)
    · simpa [mul_comm] using Nat.mul_le_mul_right B (degree v)
  have hlen : (goodIndices G f L v).length =
      ((Finset.range L).filter (fun i => Good G f v i)).card := by
    unfold goodIndices
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext i; simp
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.range L) (fun i => Good G f v i)
  simp only [Finset.card_range] at hsum
  omega

end EditMulticoloring.Dev.PrimeMC

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.PrimeMC in
theorem chk_prime_multicoloring {V : Type} [Fintype V]
    (q : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) (r B : ℕ)
    (hB : 1 ≤ B) (degree : ∀ v, (neighbors G v).card ≤ r)
    (f : V → ℕ) (range : ∀ v, f v < 2 ^ B)
    (proper : ∀ u v, G.Adj u v → f u ≠ f v) :
    let L := paletteLength r B
    let J := foldCount q L
    (∀ v, J ≤ (goodIndices G f L v).length) ∧
    (∀ v, (assigned G f L J v).card = J ∧ assigned G f L J v ⊆ palette L) ∧
    (∀ u v, G.Adj u v → Disjoint (assigned G f L J u) (assigned G f L J v))
    := by
  intro L J
  have hL : L = 4 * (r + 1) * (B + 1) := rfl
  have hL8' : 8 ≤ L := by rw [hL]; nlinarith [Nat.zero_le r, Nat.zero_le B]
  have hL8 : L / 2 ≠ 0 := by omega
  have hJ : J ≤ L / 2 := by
    have := Nat.pow_log_le_self q hL8
    simpa [J, foldCount, floorLog] using this
  have hgood : ∀ v, J ≤ (goodIndices G f L v).length := by
    intro v
    have h := good_len G r B degree f range proper L v
    have : r * B * 4 ≤ L := by rw [hL]; nlinarith [Nat.zero_le r, Nat.zero_le B]
    omega
  -- facts about colorPair
  have hgi : ∀ v i, i ∈ goodIndices G f L v ↔ i < L ∧ Good G f v i := by
    intro v i
    classical
    simp [goodIndices]
  have hnodup : ∀ v, (goodIndices G f L v).Nodup := by
    intro v; classical
    exact (List.nodup_range).filter _
  have hfst : ∀ v j, j < J → ∃ hj' : j < (goodIndices G f L v).length,
      (colorPair G f L v j).1 = (goodIndices G f L v)[j] ∧
      (colorPair G f L v j).2 = f v % primeAt (colorPair G f L v j).1 := by
    intro v j hj
    have hj' : j < (goodIndices G f L v).length := lt_of_lt_of_le hj (hgood v)
    exact ⟨hj', by simp [colorPair, List.getElem?_eq_getElem hj'], rfl⟩
  have hfmem : ∀ v j, j < J → (colorPair G f L v j).1 ∈ goodIndices G f L v := by
    intro v j hj
    obtain ⟨hj', h1, _⟩ := hfst v j hj
    exact h1 ▸ List.getElem_mem _
  refine ⟨hgood, fun v => ⟨?_, ?_⟩, ?_⟩
  · unfold assigned
    rw [List.toFinset_card_of_nodup]
    · simp
    · rw [List.nodup_map_iff_inj_on (List.nodup_range)]
      intro j hj k hk h
      have hj' := List.mem_range.1 hj
      have hk' := List.mem_range.1 hk
      have h1 := congrArg Prod.fst h
      obtain ⟨hja, hj1, _⟩ := hfst v j hj'
      obtain ⟨hka, hk1, _⟩ := hfst v k hk'
      rw [hj1, hk1] at h1
      exact (List.Nodup.getElem_inj_iff (hnodup v)).1 h1
  · intro x hx
    simp only [assigned, List.mem_toFinset, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have h1 := (hgi v _).1 (hfmem v j hj)
    obtain ⟨_, _, h2⟩ := hfst v j hj
    simp only [palette, List.mem_toFinset, List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨(colorPair G f L v j).1, h1.1, (colorPair G f L v j).2, ?_, rfl⟩
    rw [h2]; exact Nat.mod_lt _ (primeAt_prime _).pos
  · intro u v huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    simp only [assigned, List.mem_toFinset, List.mem_map, List.mem_range] at hxu hxv
    obtain ⟨j, hj, rfl⟩ := hxu
    obtain ⟨k, hk, hk2⟩ := hxv
    have h1 := (hgi u _).1 (hfmem u j hj)
    have h2 := congrArg Prod.fst hk2
    have h3 := congrArg Prod.snd hk2
    obtain ⟨_, _, e1⟩ := hfst u j hj
    obtain ⟨_, _, e2⟩ := hfst v k hk
    rw [e1, e2, h2] at h3
    exact h1.2 v huv (by first | exact h2 ▸ h3.symm | exact h2.symm ▸ h3.symm | exact h2 ▸ h3 | exact h2.symm ▸ h3)
end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_prime_multicoloring := @EditMulticoloring.Code.chk_prime_multicoloring
