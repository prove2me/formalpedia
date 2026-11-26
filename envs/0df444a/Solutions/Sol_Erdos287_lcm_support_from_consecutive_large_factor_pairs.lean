-- Prove2me | solution 1 for Erdos287.lcm_support_from_consecutive_large_factor_pairs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:53:23.859523+00:00
-- url     : https://prove2.me/submissions/eb05e9f7-90c1-4954-8395-081ceca6f80b

import Mathlib

open Finset

set_option autoImplicit false

/-- Hitting many consecutive pairs with large prime factors forces many large
prime divisors of the selected least common multiple. -/
theorem solution (D S : Finset ℕ) (M Y : ℕ) (hY : 0 < Y)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hcover : ∀ x ∈ S, x ∈ D ∨ x + 1 ∈ D)
    (hlabels : ∀ x ∈ S, ∀ n, n = x ∨ n = x + 1 →
      ∃ p : ℕ, p.Prime ∧ Y ≤ p ∧ p ∣ n) :
    let P := (Finset.Icc Y M).filter fun p => p.Prime ∧ p ∣ D.lcm id
    S.card ≤ 2 * P.card * (M / Y) ∧ Y ^ P.card ≤ D.lcm id := by
  classical
  intro P
  let B (p : ℕ) := (Icc 1 (M / Y)).image fun a => a * p
  let U := P.biUnion B
  have hlabel (x : ℕ) (hx : x ∈ S) (n : ℕ) (hn : n ∈ D)
      (hside : n = x ∨ n = x + 1) : n ∈ U := by
    obtain ⟨p, hp, hy, hd⟩ := hlabels x hx n hside
    have hpn := Nat.le_of_dvd (hD n hn).1 hd
    have hpP : p ∈ P := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hy, hpn.trans (hD n hn).2⟩, hp, hd.trans (Finset.dvd_lcm hn)⟩
    refine mem_biUnion.mpr ⟨p, hpP, mem_image.mpr ⟨n / p, ?_, Nat.div_mul_cancel hd⟩⟩
    exact mem_Icc.mpr ⟨Nat.div_pos hpn hp.pos,
      (Nat.div_le_div_right (hD n hn).2).trans (Nat.div_le_div_left hy hY)⟩
  have hsub : S ⊆ U ∪ U.image (fun n => n - 1) := by
    intro x hx
    rcases hcover x hx with h | h
    · exact mem_union_left _ (hlabel x hx x h (Or.inl rfl))
    · exact mem_union_right _ (mem_image.mpr
        ⟨x + 1, hlabel x hx (x + 1) h (Or.inr rfl), by omega⟩)
  have hU : U.card ≤ P.card * (M / Y) := by
    calc
      U.card ≤ ∑ p ∈ P, (B p).card := card_biUnion_le
      _ ≤ ∑ _ ∈ P, M / Y :=
        sum_le_sum fun p _ => card_image_le.trans (by simp)
      _ = _ := by simp
  constructor
  · calc
      S.card ≤ (U ∪ U.image (fun n => n - 1)).card := card_le_card hsub
      _ ≤ U.card + (U.image (fun n => n - 1)).card := card_union_le _ _
      _ ≤ U.card + U.card := Nat.add_le_add_left card_image_le _
      _ ≤ 2 * P.card * (M / Y) := by rw [Nat.mul_assoc]; omega
  · have hprod : (∏ p ∈ P, p) ∣ D.lcm id := by
      apply Int.natCast_dvd_natCast.mp
      rw [Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ fun p hp => Int.natCast_dvd_natCast.mpr (mem_filter.mp hp).2.2
      intro p hp q hq hpq
      exact Nat.isCoprime_iff_coprime.mpr
        ((Nat.coprime_primes (mem_filter.mp hp).2.1 (mem_filter.mp hq).2.1).mpr hpq)
    have hLpos : 0 < D.lcm id :=
      Nat.pos_of_dvd_of_pos (D.lcm_dvd_prod id) (prod_pos fun n hn => (hD n hn).1)
    calc
      Y ^ P.card = ∏ _ ∈ P, Y := by simp
      _ ≤ ∏ p ∈ P, p := prod_le_prod' fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).1
      _ ≤ D.lcm id := Nat.le_of_dvd hLpos hprod

