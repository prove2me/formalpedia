-- Prove2me | solution 1 for Erdos287.large_prime_omission_mass
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:00:50.816743+00:00
-- url     : https://prove2.me/submissions/f3e70b4d-dcef-4985-a434-7f3980819a36

import Mathlib
import Theorems.Thm_Erdos287_large_prime_product_divides_reciprocal_denominator
import Theorems.Thm_Erdos287_log_ratio_lower_bound_from_omissions

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Distinct large-prime layers have disjoint mass. The entire harmonic
mass of their omitted cofactors enters the required interval ratio. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, (f (k - 1) / p) * Nat.lcmUpto (f (k - 1) / p) < p) :
    let m := f 0
    let M := f (k - 1)
    (1 : ℝ) + ∑ p ∈ P, (1 : ℝ) / p *
      ∑ a ∈ (Finset.Icc 1 (M / p)).filter (fun a => m ≤ a * p), (1 : ℝ) / a ≤
      Real.log ((M : ℝ) / ((m - 1 : ℕ) : ℝ)) := by
  classical
  intro m M
  let D := (range k).image f
  let L (p : ℕ) := (Icc m M).filter (fun n => p ∣ n)
  let C (p : ℕ) := (Icc 1 (M / p)).filter (fun a => m ≤ a * p)
  have hm : 0 < m := hfirst.pos
  have hmodel (n : ℕ) (hn : n ∈ D) : m ≤ n ∧ n ≤ M := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hlt := mem_range.mp hi
    constructor
    · rcases Nat.eq_zero_or_pos i with rfl | hip
      · exact le_rfl
      · exact (hmono 0 i hip hlt).le
    · rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with he | hl
      · rw [he]
      · exact (hmono i (k - 1) hl (by omega)).le
  have hinj : Set.InjOn f (↑(range k) : Set ℕ) := by
    intro i hi j hj he
    have hi' := mem_range.mp (show i ∈ range k from hi)
    have hj' := mem_range.mp (show j ∈ range k from hj)
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((hmono i j hij hj').ne he).elim
    · exact hij
    · exact ((hmono j i hij hi').ne he.symm).elim
  have hsumD : ∑ n ∈ D, (1 : ℚ) / n = 1 := by
    change (∑ n ∈ (range k).image f, (1 : ℚ) / n) = 1
    rw [sum_image (fun _ hi _ hj he => hinj hi hj he), hsum]
  have hbig (p : ℕ) (hp : p ∈ P) : M < p * p := by
    have hB : M / p < p := (Nat.le_mul_of_pos_right _ (Nat.lcmUpto_pos (M / p))).trans_lt (hsmall p hp)
    exact (Nat.div_lt_iff_lt_mul (hP p hp).pos).mp hB
  have hno (p : ℕ) (hp : p ∈ P) (n : ℕ) (hn : n ∈ D) : ¬ p ∣ n := by
    intro hd
    have hden := Erdos287.large_prime_product_divides_reciprocal_denominator D {p} M
      (fun k hk => ⟨hm.trans_le (hmodel k hk).1, (hmodel k hk).2⟩)
      (fun q hq => by have he := mem_singleton.mp hq; subst q; exact hP p hp)
      (fun q hq => by have he := mem_singleton.mp hq; subst q; exact hsmall p hp)
      (fun q hq => by have he := mem_singleton.mp hq; subst q; exact ⟨n, hn, hd⟩)
    rw [prod_singleton, hsumD, Rat.den_one] at hden
    exact (hP p hp).not_dvd_one hden
  have hpairs : (↑P : Set ℕ).PairwiseDisjoint L := by
    intro p hp r hr hne
    apply disjoint_left.mpr
    intro n hpN hrN
    obtain ⟨hI, hpd⟩ := mem_filter.mp hpN
    have hn := mem_Icc.mp hI
    have hrd := (mem_filter.mp hrN).2
    have hcop := (Nat.coprime_primes (hP p hp) (hP r hr)).mpr hne
    have ht := Nat.le_of_dvd (hm.trans_le hn.1) (hcop.mul_dvd_of_dvd_of_dvd hpd hrd)
    rcases le_total p r with h | h
    · exact (hbig p hp).not_ge ((Nat.mul_le_mul_left _ h).trans (ht.trans hn.2))
    · exact (hbig r hr).not_ge ((Nat.mul_le_mul_right _ h).trans (ht.trans hn.2))
  have hC (p : ℕ) (hp : p ∈ P) : (C p).image (fun a => a * p) = L p := by
    ext n
    constructor
    · intro hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
      obtain ⟨ha', hl⟩ := mem_filter.mp ha
      have hu := (Nat.le_div_iff_mul_le (hP p hp).pos).mp (mem_Icc.mp ha').2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, hu⟩, dvd_mul_left _ _⟩
    · intro hn
      obtain ⟨hi, ⟨a, he⟩⟩ := mem_filter.mp hn
      have hp0 := (hP p hp).pos
      have he' : a * p = n := by simpa only [mul_comm] using he.symm
      have ha : 0 < a := by
        have hn' := hm.trans_le (mem_Icc.mp hi).1
        exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at he'; omega)
      have hau : a ≤ M / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (he'.symm ▸ (mem_Icc.mp hi).2)
      exact mem_image.mpr ⟨a, mem_filter.mpr
        ⟨mem_Icc.mpr ⟨ha, hau⟩, he'.symm ▸ (mem_Icc.mp hi).1⟩, he'⟩
  let H := P.biUnion L
  have hH (n : ℕ) (hn : n ∈ H) : m ≤ n ∧ n ≤ M := by
    obtain ⟨p, hp, hpn⟩ := mem_biUnion.mp hn
    exact mem_Icc.mp (mem_filter.mp hpn).1
  have hmiss (i : ℕ) (hi : i < k) : f i ∉ H := by
    intro hn
    obtain ⟨p, hp, hpn⟩ := mem_biUnion.mp hn
    exact hno p hp _ (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩) (mem_filter.mp hpn).2
  have hmass : (∑ n ∈ H, (1 : ℝ) / n) =
      ∑ p ∈ P, (1 : ℝ) / p * ∑ a ∈ C p, (1 : ℝ) / a := by
    rw [show H = P.biUnion L from rfl, sum_biUnion hpairs]
    apply sum_congr rfl
    intro p hp
    rw [← hC p hp, sum_image (fun a _ b _ he =>
      Nat.eq_of_mul_eq_mul_right (hP p hp).pos he), mul_sum]
    apply sum_congr rfl
    intro a ha
    push_cast
    rw [one_div_mul_one_div, mul_comm (p : ℝ)]
  have hratio := Erdos287.log_ratio_lower_bound_from_omissions k hk f hfirst hmono hsum H hH hmiss
  rw [hmass] at hratio
  exact hratio

