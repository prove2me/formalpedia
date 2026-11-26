-- Prove2me | solution 1 for Erdos287.chen_switching_triples_from_rough_factor_set
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:18:36.713729+00:00
-- url     : https://prove2.me/submissions/22aebe4e-a6ad-4e6a-a12f-4f941837318a

import Mathlib

open Finset

set_option autoImplicit false

/-- For a rough integer with squarefree medium prime factors, fixing the two
least such factors gives one admissible switching triple for each remaining one. -/
theorem solution (n Y Z : ℕ) (hn : 0 < n)
    (hrough : ∀ l : ℕ, l.Prime → l ∣ n → Y < l)
    (hsquare : ∀ l : ℕ, l.Prime → Y < l → l ≤ Z → ¬ l ^ 2 ∣ n) :
    let S := n.primeFactors.filter (fun l => Y < l ∧ l ≤ Z)
    let triples := (Finset.product (Finset.product S S) S).filter (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧
      ∃ s ∈ Finset.range (n + 1), n = t.1.1 * t.1.2 * t.2 * s ∧
        ∀ l ∈ s.primeFactors, t.1.2 ≤ l)
    2 * (if S.card = 0 then 1 else 0) + S.card ≤ 2 + triples.card := by
  classical
  dsimp only
  let S := n.primeFactors.filter (fun l => Y < l ∧ l ≤ Z)
  let triples := ((S ×ˢ S) ×ˢ S).filter (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧
    ∃ s ∈ Finset.range (n + 1), n = t.1.1 * t.1.2 * t.2 * s ∧
      ∀ l ∈ s.primeFactors, t.1.2 ≤ l)
  change 2 * (if S.card = 0 then 1 else 0) + S.card ≤ 2 + triples.card
  by_cases hsize : S.card ≤ 2
  · split <;> omega
  have hS : S.Nonempty := card_pos.mp (by omega)
  let p := S.min' hS
  have hpS : p ∈ S := min'_mem S hS
  let rest := S.erase p
  have hrest : rest.card = S.card - 1 := card_erase_of_mem hpS
  have hR : rest.Nonempty := card_pos.mp (by omega)
  let q := rest.min' hR
  have hqR : q ∈ rest := min'_mem rest hR
  have hqS : q ∈ S := mem_of_mem_erase hqR
  have hpq : p < q := lt_of_le_of_ne (min'_le S q hqS) (ne_of_mem_erase hqR).symm
  have hprime (j : ℕ) (hj : j ∈ S) : j.Prime :=
    Nat.prime_of_mem_primeFactors (mem_filter.mp hj).1
  have hdiv (j : ℕ) (hj : j ∈ S) : j ∣ n :=
    Nat.dvd_of_mem_primeFactors (mem_filter.mp hj).1
  have hcop (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : a.Coprime b :=
    (Nat.coprime_primes (hprime a ha) (hprime b hb)).2 hne
  let embed : ℕ ↪ (ℕ × ℕ) × ℕ := ⟨fun r => ((p, q), r), fun _ _ h => congrArg Prod.snd h⟩
  have hsub : (rest.erase q).map embed ⊆ triples := by
    intro pair ht
    obtain ⟨r, hr, rfl⟩ := mem_map.mp ht
    have hrR := mem_of_mem_erase hr
    have hrS := mem_of_mem_erase hrR
    have hqr : q < r := lt_of_le_of_ne (min'_le rest r hrR) (ne_of_mem_erase hr).symm
    have hpr := hpq.trans hqr
    have hpqd := (hcop p q hpS hqS hpq.ne).mul_dvd_of_dvd_of_dvd (hdiv p hpS) (hdiv q hqS)
    have hpr_dvd : p * q * r ∣ n :=
      ((hcop p r hpS hrS hpr.ne).mul_left (hcop q r hqS hrS hqr.ne)).mul_dvd_of_dvd_of_dvd
        hpqd (hdiv r hrS)
    obtain ⟨s, hrs⟩ := hpr_dvd
    have hspos : 0 < s := Nat.pos_of_ne_zero (fun he => by rw [he, mul_zero] at hrs; omega)
    have hsn : s ∣ n := ⟨p * q * r, hrs.trans (mul_comm _ _)⟩
    have hsl : ∀ l ∈ s.primeFactors, q ≤ l := by
      intro l hl
      by_contra! hlt
      have hld := Nat.dvd_of_mem_primeFactors hl
      have hln := hld.trans hsn
      have hlprime := Nat.prime_of_mem_primeFactors hl
      have hls : l ∈ S := mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hlprime, hln, hn.ne'⟩,
          hrough l hlprime hln, hlt.le.trans (mem_filter.mp hqS).2.2⟩
      have hlp : l = p := by
        by_contra hne
        exact hlt.not_ge (min'_le rest l (mem_erase.mpr ⟨hne, hls⟩))
      subst l
      obtain ⟨u, hu⟩ := hld
      apply hsquare p (hprime p hpS) (mem_filter.mp hpS).2.1 (mem_filter.mp hpS).2.2
      refine ⟨q * r * u, ?_⟩
      rw [hrs, hu, pow_two]
      ac_rfl
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_product.mpr ⟨hpS, hqS⟩, hrS⟩,
      hpq, hqr, s, mem_range.mpr ?_, hrs, hsl⟩
    exact Nat.lt_succ_of_le (Nat.le_of_dvd hn hsn)
  have hc := card_le_card hsub
  rw [card_map, card_erase_of_mem hqR, hrest] at hc
  simp only [if_neg (show S.card ≠ 0 from by omega), mul_zero, zero_add]
  omega

