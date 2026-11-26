-- Prove2me | solution 1 for Erdos287.disjoint_large_prime_layer_repairs_can_be_combined
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:37:22.668128+00:00
-- url     : https://prove2.me/submissions/7beb11b6-c8db-4e81-87df-2b60e02c1a40

import Mathlib

open Finset

set_option autoImplicit false

private theorem sum_den_not_dvd (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ n ∈ S, ¬ p ∣ (f n).den) : ¬ p ∣ (∑ n ∈ S, f n).den := by
  induction S using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | insert n S hn ih =>
    rw [sum_insert hn]
    intro hd
    have hs := ih (fun k hk => hf k (mem_insert_of_mem hk))
    exact hp.not_dvd_lcm (hf n (mem_insert_self _ _)) hs
      (hd.trans (Rat.add_den_dvd_lcm (f n) (∑ k ∈ S, f k)))

private theorem recip_den_dvd (n : ℕ) : ((1 : ℚ) / n).den ∣ n := by
  have he : (1 : ℚ) / n = Rat.divInt 1 (n : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_one]
  rw [he]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd 1 (n : ℤ))

/-- Local denominator repairs in large-prime layers can be made simultaneously,
using odd omissions that avoid the neighbors of earlier holes. -/
theorem solution (I H P : Finset ℕ) (A : ℕ → Finset ℕ) (M Y : ℕ)
    (hI : ∀ n ∈ I, 0 < n ∧ n ≤ M)
    (hH : H ⊆ I) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p) (hSq : M < Y ^ 2)
    (hA : ∀ p ∈ P, ∀ n ∈ A p,
      n ∈ I ∧ p ∣ n ∧ Odd n ∧ n ∉ H ∧ n - 1 ∉ H ∧ n + 1 ∉ H)
    (hrepair : ∀ p ∈ P, ∃ T ⊆ A p,
      ¬ p ∣ (∑ n ∈ (I.filter (fun n => p ∣ n)) \ (H ∪ T), (1 : ℚ) / n).den) :
    ∃ O ⊆ I, H ⊆ O ∧ (∀ n ∈ O, n + 1 ∉ O) ∧
      (∀ p ∈ P, ¬ p ∣ (∑ n ∈ I \ O, (1 : ℚ) / n).den) ∧
      (O \ H).card ≤ ∑ p ∈ P, (A p).card := by
  classical
  choose T hT hclear using hrepair
  let R := P.attach.biUnion (fun p => T p.val p.property)
  let O := H ∪ R
  have hR (n : ℕ) (hn : n ∈ R) : n ∈ I ∧ Odd n ∧ n ∉ H ∧ n - 1 ∉ H ∧ n + 1 ∉ H := by
    obtain ⟨p, _, hnT⟩ := mem_biUnion.mp hn
    obtain ⟨h₁, _, h₂, h₃, h₄, h₅⟩ := hA p.val p.property n (hT _ _ hnT)
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hTCover (p : ℕ) (hp : p ∈ P) : T p hp ⊆ R := by
    intro n hn
    exact mem_biUnion.mpr ⟨⟨p, hp⟩, mem_attach _ _, hn⟩
  have hsame (p : ℕ) (hp : p ∈ P) (n : ℕ) (hnI : n ∈ I)
      (hpn : p ∣ n) (hnR : n ∈ R) : n ∈ T p hp := by
    obtain ⟨q, _, hnq⟩ := mem_biUnion.mp hnR
    have hqn := (hA q.val q.property n (hT _ _ hnq)).2.1
    have he : q.val = p := by
      by_contra hne
      have hcop := (Nat.coprime_primes (hP q.val q.property).1 (hP p hp).1).mpr hne
      have hd := hcop.mul_dvd_of_dvd_of_dvd hqn hpn
      have hlow : Y ^ 2 ≤ q.val * p := by
        rw [pow_two]
        exact Nat.mul_le_mul (hP _ q.property).2 (hP _ hp).2
      exact (hSq.trans_le (hlow.trans (Nat.le_of_dvd (hI n hnI).1 hd))).not_ge (hI n hnI).2
    have hq : q = (⟨p, hp⟩ : ↥P) := Subtype.ext he
    simpa only [hq] using hnq
  refine ⟨O, union_subset hH (fun n hn => (hR n hn).1), subset_union_left, ?_, ?_, ?_⟩
  · intro n hn hsucc
    rcases mem_union.mp hn with hnH | hnR <;> rcases mem_union.mp hsucc with hsH | hsR
    · exact hsep n hnH hsH
    · exact (hR _ hsR).2.2.2.1 (by simpa using hnH)
    · exact (hR _ hnR).2.2.2.2 hsH
    · obtain ⟨i, hi⟩ := (hR _ hnR).2.1
      obtain ⟨j, hj⟩ := (hR _ hsR).2.1
      omega
  · intro p hp
    let D := I \ O
    let Lay := D.filter (fun n => p ∣ n)
    let Other := D.filter (fun n => ¬ p ∣ n)
    have hLay : Lay = (I.filter (fun n => p ∣ n)) \ (H ∪ T p hp) := by
      ext n
      constructor
      · intro hn
        obtain ⟨hnD, hpn⟩ := mem_filter.mp hn
        obtain ⟨hnI, hnO⟩ := mem_sdiff.mp hnD
        refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hnI, hpn⟩, ?_⟩
        intro h
        rcases mem_union.mp h with hh | ht
        · exact hnO (mem_union_left _ hh)
        · exact hnO (mem_union_right _ (hTCover p hp ht))
      · intro hn
        obtain ⟨hnI, hnT⟩ := mem_sdiff.mp hn
        obtain ⟨hnI, hpn⟩ := mem_filter.mp hnI
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨hnI, ?_⟩, hpn⟩
        intro ho
        rcases mem_union.mp ho with hh | hr
        · exact hnT (mem_union_left _ hh)
        · exact hnT (mem_union_right _ (hsame p hp n hnI hpn hr))
    have hpL : ¬ p ∣ (∑ n ∈ Lay, (1 : ℚ) / n).den := by rw [hLay]; exact hclear p hp
    have hpO : ¬ p ∣ (∑ n ∈ Other, (1 : ℚ) / n).den := by
      apply sum_den_not_dvd p (hP p hp).1
      intro n hn hd
      exact (mem_filter.mp hn).2 (hd.trans (recip_den_dvd n))
    have he := sum_filter_add_sum_filter_not D (fun n => p ∣ n) (fun n => (1 : ℚ) / n)
    change (∑ n ∈ Lay, (1 : ℚ) / n) + (∑ n ∈ Other, (1 : ℚ) / n) =
      (∑ n ∈ D, (1 : ℚ) / n) at he
    change ¬ p ∣ (∑ n ∈ D, (1 : ℚ) / n).den
    rw [← he]
    exact fun hd => (hP p hp).1.not_dvd_lcm hpL hpO (hd.trans (Rat.add_den_dvd_lcm _ _))
  · have hsub : O \ H ⊆ R := by
      intro n hn
      obtain ⟨hnO, hnH⟩ := mem_sdiff.mp hn
      exact (mem_union.mp hnO).resolve_left hnH
    calc
      (O \ H).card ≤ R.card := card_le_card hsub
      _ ≤ ∑ p ∈ P.attach, (T p.val p.property).card := card_biUnion_le
      _ ≤ ∑ p ∈ P.attach, (A p.val).card := sum_le_sum fun p _ => card_le_card (hT p.val p.property)
      _ = _ := sum_attach P (fun p => (A p).card)

