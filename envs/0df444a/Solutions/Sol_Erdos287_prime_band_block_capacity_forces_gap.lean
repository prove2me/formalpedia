-- Prove2me | solution 1 for Erdos287.prime_band_block_capacity_forces_gap
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:31:42.505532+00:00
-- url     : https://prove2.me/submissions/e1276b41-3951-4bce-92db-d7cbc95d88e9

import Mathlib
import Theorems.Thm_Erdos287_few_prime_layers_with_few_omissions

open Finset

set_option autoImplicit false

/-- Disjoint blocks of one or two consecutive available positions constrain
the omissions of several prime layers jointly. -/
theorem solution (D H P U J : Finset ℕ) (block : ℕ → ℕ)
    (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1))
    (hcover : ∀ n ∈ Finset.Icc m M, n - 1 ∉ H → n + 1 ∉ H →
      (∃ p ∈ P, p ∣ n) → n ∈ U)
    (hblock : ∀ n ∈ U, block n ∈ J)
    (hpair : ∀ x ∈ U, ∀ y ∈ U, block x = block y →
      x = y ∨ x + 1 = y ∨ y + 1 = x)
    (hsmall :
      J.card < R * (P.card - ((B + 1) * (B + 1)) *
        (∑ j ∈ Finset.range R, B.choose j) * K)) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by
  classical
  by_contra hno
  let A (p : ℕ) := (Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)
  let T (p : ℕ) := (A p).image (fun c => c * p)
  let Good := P.filter (fun p => R ≤ (A p).card)
  let X := Good.biUnion T
  let E := ((B + 1) * (B + 1)) * (∑ j ∈ range R, B.choose j) * K
  change J.card < R * (P.card - E) at hsmall
  have hGoodP : Good ⊆ P := filter_subset _ _
  have hbad : (P.filter (fun p => (A p).card < R)).card ≤ E :=
    Erdos287.few_prime_layers_with_few_omissions D P m M B Y K R hm hmM hD hsum hY hP hbound
  have hsplit : Good.card + (P.filter (fun p => (A p).card < R)).card = P.card := by
    simpa only [Good, not_le] using P.card_filter_add_card_filter_not (fun p => R ≤ (A p).card)
  have hgood : P.card - E ≤ Good.card := by omega
  have hT (p : ℕ) (hp : p ∈ P) (n : ℕ) (hn : n ∈ T p) :
      n ∈ Icc m M ∧ n ∉ D ∧ p ∣ n := by
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hn
    obtain ⟨hcC, hcD⟩ := mem_filter.mp hc
    obtain ⟨hcl, hcu⟩ := mem_Icc.mp hcC
    have hp0 := (hP p hp).1.pos
    have hlo : m - 1 < c * p := (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_of_succ_le hcl)
    have hhi : c * p ≤ M := (Nat.le_div_iff_mul_le hp0).mp hcu
    exact ⟨mem_Icc.mpr ⟨by omega, hhi⟩, hcD, dvd_mul_left p c⟩
  have hTdisj : (↑Good : Set ℕ).PairwiseDisjoint T := by
    intro p hp q hq hpq
    refine disjoint_left.mpr fun n hnp hnq => ?_
    have hpP := hGoodP hp
    have hqP := hGoodP hq
    obtain ⟨hn, _, hpd⟩ := hT p hpP n hnp
    have hqd := (hT q hqP n hnq).2.2
    have hcop := (Nat.coprime_primes (hP p hpP).1 (hP q hqP).1).mpr hpq
    have hprod := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hlow : Y ^ 2 ≤ p * q := by
      rw [pow_two]
      exact Nat.mul_le_mul (hP p hpP).2.1 (hP q hqP).2.1
    obtain ⟨hnl, hnu⟩ := mem_Icc.mp hn
    exact (hYM.trans_le (hlow.trans (Nat.le_of_dvd (hm.trans_le hnl) hprod))).not_ge hnu
  have hR (p : ℕ) (hp : p ∈ Good) : R ≤ (T p).card := by
    have hp0 := (hP p (hGoodP hp)).1.pos
    rw [show T p = (A p).image (fun c => c * p) from rfl,
      card_image_of_injOn (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hp0 he)]
    exact (mem_filter.mp hp).2
  have hXlow : R * (P.card - E) ≤ X.card := calc
    _ ≤ R * Good.card := Nat.mul_le_mul_left _ hgood
    _ = ∑ _ ∈ Good, R := by simp [mul_comm]
    _ ≤ ∑ p ∈ Good, (T p).card := sum_le_sum hR
    _ = _ := (card_biUnion hTdisj).symm
  have hX (n : ℕ) (hn : n ∈ X) : n ∈ Icc m M ∧ n ∉ D ∧ n ∈ U := by
    obtain ⟨p, hp, hnT⟩ := mem_biUnion.mp hn
    obtain ⟨hnI, hnD, hpn⟩ := hT p (hGoodP hp) n hnT
    refine ⟨hnI, hnD, hcover n hnI ?_ ?_ ⟨p, hGoodP hp, hpn⟩⟩
    · intro hleft
      have hnl := (mem_Icc.mp hnI).1
      have hnu := (mem_Icc.mp hnI).2
      have he : n - 1 + 1 = n := by omega
      exact hno ⟨n - 1, (mem_Icc.mp (hH hleft)).1, he.symm ▸ hnu,
        disjoint_left.mp hHD hleft, he.symm ▸ hnD⟩
    · intro hright
      exact hno ⟨n, (mem_Icc.mp hnI).1, (mem_Icc.mp (hH hright)).2, hnD,
        disjoint_left.mp hHD hright⟩
  have hmap : Set.MapsTo block (↑X : Set ℕ) (↑J : Set ℕ) :=
    fun n hn => hblock n (hX n hn).2.2
  have hinj : Set.InjOn block (↑X : Set ℕ) := by
    intro x hx y hy hxy
    obtain ⟨hxI, hxD, hxU⟩ := hX x hx
    obtain ⟨hyI, hyD, hyU⟩ := hX y hy
    rcases hpair x hxU y hyU hxy with h | h | h
    · exact h
    · exact (hno ⟨x, (mem_Icc.mp hxI).1, h.symm ▸ (mem_Icc.mp hyI).2,
        hxD, h.symm ▸ hyD⟩).elim
    · exact (hno ⟨y, (mem_Icc.mp hyI).1, h.symm ▸ (mem_Icc.mp hxI).2,
        hyD, h.symm ▸ hxD⟩).elim
  exact hsmall.not_ge (hXlow.trans (card_le_card_of_injOn block hmap hinj))

