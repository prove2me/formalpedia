-- Prove2me | solution 1 for Erdos287.sparse_prime_power_layer
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:48:15.8598+00:00
-- url     : https://prove2.me/submissions/2961cff5-90bc-4e68-b9d7-8d671d76f754

import Mathlib
import Theorems.Thm_Erdos287_reciprocal_cut_lattice

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem prime_power_not_dvd_lcm (S : Finset ℕ) (p e : ℕ)
    (hp : p.Prime) (he : 1 ≤ e) (hpos : ∀ n ∈ S, 0 < n)
    (havoid : ∀ n ∈ S, ¬ p ^ e ∣ n) : ¬ p ^ e ∣ S.lcm id := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty, hp.pow_dvd_iff_le_factorization Nat.one_ne_zero,
      Nat.factorization_one, Finsupp.zero_apply]
    omega
  | @insert n S hn ih =>
    have hnp : 0 < n := hpos n (mem_insert_self n S)
    have hSpos : S.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr
      (fun j hj => (hpos j (mem_insert_of_mem hj)).ne')
    have hnot : ¬ p ^ e ∣ S.lcm id :=
      ih (fun j hj => hpos j (mem_insert_of_mem hj)) (fun j hj => havoid j (mem_insert_of_mem hj))
    have hl : n.lcm (S.lcm id) ≠ 0 := Nat.lcm_ne_zero hnp.ne' hSpos
    have hna : n.factorization p < e :=
      lt_of_not_ge (fun he' => havoid n (mem_insert_self n S)
        ((hp.pow_dvd_iff_le_factorization hnp.ne').mpr he'))
    have hnb : (S.lcm id).factorization p < e :=
      lt_of_not_ge (fun he' => hnot ((hp.pow_dvd_iff_le_factorization hSpos).mpr he'))
    rw [Finset.lcm_insert]
    change ¬ p ^ e ∣ n.lcm (S.lcm id)
    rw [hp.pow_dvd_iff_le_factorization hl, Nat.factorization_lcm hnp.ne' hSpos, Finsupp.sup_apply]
    exact (max_lt hna hnb).not_ge

private theorem den_div_of_coprime (a b : ℕ) (hb : b ≠ 0) (h : a.Coprime b) :
    ((a : ℚ) / b).den = b := by
  have he : (a : ℚ) / b = Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  rw [he, Rat.den_divInt]
  norm_cast
  simp [hb, h.gcd_eq_one, Nat.gcd_comm b a]

/-- A high prime power with at most two adjacent cofactors from `1,2,3`
can survive only in the two listed cancellation pairs. -/
theorem solution (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hspan : M < m + 2 * p ^ e) (hmax : M < 4 * p ^ e) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ (p = 3 ∧ H = ({q, 2 * q} : Finset ℕ)) ∨
      (p = 5 ∧ H = ({2 * q, 3 * q} : Finset ℕ)) := by
  classical
  dsimp only
  let q := p ^ e
  let H := D.filter (fun n => q ∣ n)
  let T := D.filter (fun n => ¬ q ∣ n)
  change H = ∅ ∨ (p = 3 ∧ H = {q, 2 * q}) ∨ (p = 5 ∧ H = {2 * q, 3 * q})
  have hq : 0 < q := pow_pos hp.pos _
  have hlow (n : ℕ) (hn : n ∈ D) : m ≤ n := (mem_Icc.mp (hD hn)).1
  have hhigh (n : ℕ) (hn : n ∈ D) : n ≤ M := (mem_Icc.mp (hD hn)).2
  have hDH : H ⊆ D := filter_subset _ _
  have hDT : T ⊆ D := filter_subset _ _
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hm.trans_le (hlow n hn)
  have hcandidates : H ⊆ ({q, 2 * q, 3 * q} : Finset ℕ) := by
    intro n hn
    obtain ⟨c, hc⟩ := (mem_filter.mp hn).2
    have hcpos : c ≠ 0 := fun h => by simp [h] at hc; exact (hpos n (hDH hn)).ne' hc
    have hclt : c < 4 := Nat.lt_of_mul_lt_mul_left (by
      rw [← hc, mul_comm q 4]
      exact (hhigh n (hDH hn)).trans_lt hmax)
    have hcofs : c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases hcofs with rfl | rfl | rfl <;> simp [hc, mul_comm]
  have hnonends : ¬ (q ∈ H ∧ 3 * q ∈ H) := by
    intro ⟨ha, hb⟩
    have hml := hlow q (hDH ha)
    have hMh := hhigh (3 * q) (hDH hb)
    change M < m + 2 * q at hspan
    omega
  have hdisj : Disjoint H T := by
    apply disjoint_left.mpr
    intro n hn ht
    exact (mem_filter.mp ht).2 (mem_filter.mp hn).2
  have hsplit : D ⊆ H ∪ T := by
    intro n hn
    by_cases hd : q ∣ n
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, hd⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, hd⟩)
  have ha : H.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun j hj => (hpos j (hDH hj)).ne')
  have hb : T.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun j hj => (hpos j (hDT hj)).ne')
  have hshare := (Erdos287.reciprocal_cut_lattice D H T (H.lcm id) (T.lcm id)
    (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
    (fun j hj => Finset.dvd_lcm hj) (fun j hj => Finset.dvd_lcm hj) hdisj hsplit 1 hsum).2 rfl
  have hDint : D ∩ H = H := inter_eq_right.mpr hDH
  have hden : (∑ n ∈ H, (1 : ℚ) / n).den ∣ T.lcm id := by
    have hh := hshare.1
    rw [hDint] at hh
    exact hh.trans (Nat.gcd_dvd_right _ _)
  have hTavoid : ¬ q ∣ T.lcm id := prime_power_not_dvd_lcm T p e hp he
    (fun n hn => hpos n (hDT hn)) (fun n hn => (mem_filter.mp hn).2)
  have hnotden : ¬ q ∣ (∑ n ∈ H, (1 : ℚ) / n).den := fun hd => hTavoid (hd.trans hden)
  have Hcases : H = ∅ ∨ H = {q} ∨ H = {2 * q} ∨ H = {3 * q} ∨
      H = {q, 2 * q} ∨ H = {2 * q, 3 * q} := by
    have heq : H = ({q, 2 * q, 3 * q} : Finset ℕ).filter (fun x => x ∈ H) := by
      ext n
      simp only [mem_filter]
      exact ⟨fun hn => ⟨hcandidates hn, hn⟩, And.right⟩
    by_cases h₁ : q ∈ H <;> by_cases h₂ : 2 * q ∈ H <;> by_cases h₃ : 3 * q ∈ H <;>
      simp [filter_insert, filter_singleton, h₁, h₂, h₃] at heq <;>
      first | exact (hnonends ⟨h₁, h₃⟩).elim | tauto
  rcases Hcases with h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    apply hnotden
    rw [h, sum_singleton, ← Nat.cast_one, den_div_of_coprime 1 q hq.ne' (Nat.coprime_one_left q)]
  · exfalso
    apply hnotden
    rw [h, sum_singleton, ← Nat.cast_one, den_div_of_coprime 1 (2 * q) (by omega) (Nat.coprime_one_left _)]
    exact dvd_mul_left q 2
  · exfalso
    apply hnotden
    rw [h, sum_singleton, ← Nat.cast_one, den_div_of_coprime 1 (3 * q) (by omega) (Nat.coprime_one_left _)]
    exact dvd_mul_left q 3
  · by_cases hn : p = 3
    · exact Or.inr (Or.inl ⟨hn, h⟩)
    exfalso
    apply hnotden
    have hc : Nat.Coprime 3 (2 * q) := (show Nat.Coprime 3 2 by decide).mul_right
      (((Nat.coprime_primes (by decide : Nat.Prime 3) hp).2 (Ne.symm hn)).pow_right e)
    have hs : (∑ n ∈ H, (1 : ℚ) / n) = (3 : ℚ) / (2 * q : ℕ) := by
      rw [h, sum_insert (by simp; omega), sum_singleton]
      push_cast
      have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp <;> ring
    have hden' : ((3 : ℚ) / (2 * q : ℕ)).den = 2 * q := by
      simpa only [Nat.cast_ofNat] using den_div_of_coprime 3 (2 * q) (by omega) hc
    rw [hs, hden']
    exact dvd_mul_left q 2
  · by_cases hn : p = 5
    · exact Or.inr (Or.inr ⟨hn, h⟩)
    exfalso
    apply hnotden
    have hc : Nat.Coprime 5 (6 * q) := (show Nat.Coprime 5 6 by decide).mul_right
      (((Nat.coprime_primes (by decide : Nat.Prime 5) hp).2 (Ne.symm hn)).pow_right e)
    have hs : (∑ n ∈ H, (1 : ℚ) / n) = (5 : ℚ) / (6 * q : ℕ) := by
      rw [h, sum_insert (by simp; omega), sum_singleton]
      push_cast
      have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp <;> ring
    have hden' : ((5 : ℚ) / (6 * q : ℕ)).den = 6 * q := by
      simpa only [Nat.cast_ofNat] using den_div_of_coprime 5 (6 * q) (by omega) hc
    rw [hs, hden']
    exact dvd_mul_left q 6

