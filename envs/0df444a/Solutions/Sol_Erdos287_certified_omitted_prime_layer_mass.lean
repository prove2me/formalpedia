-- Prove2me | solution 1 for Erdos287.certified_omitted_prime_layer_mass
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:13:25.348938+00:00
-- url     : https://prove2.me/submissions/e07a3e98-a921-46ad-b606-76e2e4bab3eb

import Mathlib
import Theorems.Thm_Erdos287_log_ratio_lower_bound_from_omissions

open Finset

set_option autoImplicit false

/-- Any certified omitted prime layers above the square-root threshold can
be added as separate terms in the reciprocal mass lower bound. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hfirst : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ f (k - 1) < p * p)
    (habsent : ∀ p ∈ P, ∀ i < k, ¬ p ∣ f i) :
    let m := f 0
    let M := f (k - 1)
    (1 : ℝ) + ∑ p ∈ P, (1 : ℝ) / p *
      ∑ a ∈ (Finset.Icc 1 (M / p)).filter (fun a => m ≤ a * p), (1 : ℝ) / a ≤
      Real.log ((M : ℝ) / ((m - 1 : ℕ) : ℝ)) := by
  classical
  intro m M
  let layer (p : ℕ) := (Icc m M).filter (fun n => p ∣ n)
  let cofactors (p : ℕ) := (Icc 1 (M / p)).filter (fun a => m ≤ a * p)
  have hpositive : 0 < m := hfirst.pos
  have hdisjoint : (↑P : Set ℕ).PairwiseDisjoint layer := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro n hn hn'
    obtain ⟨hi, hpd⟩ := mem_filter.mp hn
    have hinterval := mem_Icc.mp hi
    have hqd := (mem_filter.mp hn').2
    have hcop := (Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq
    have hprod := Nat.le_of_dvd (hpositive.trans_le hinterval.1)
      (hcop.mul_dvd_of_dvd_of_dvd hpd hqd)
    rcases le_total p q with hpq' | hqp'
    · exact (hP p hp).2.not_ge ((Nat.mul_le_mul_left p hpq').trans (hprod.trans hinterval.2))
    · exact (hP q hq).2.not_ge ((Nat.mul_le_mul_right q hqp').trans (hprod.trans hinterval.2))
  have himage (p : ℕ) (hp : p ∈ P) : (cofactors p).image (fun a => a * p) = layer p := by
    have hp0 := (hP p hp).1.pos
    ext n
    constructor
    · intro hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
      obtain ⟨ha', hl⟩ := mem_filter.mp ha
      have hu := (Nat.le_div_iff_mul_le hp0).mp (mem_Icc.mp ha').2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, hu⟩, dvd_mul_left _ _⟩
    · intro hn
      obtain ⟨hi, ⟨a, he⟩⟩ := mem_filter.mp hn
      have he' : a * p = n := by simpa only [mul_comm] using he.symm
      have ha : 0 < a := by
        have hn' := hpositive.trans_le (mem_Icc.mp hi).1
        exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at he'; omega)
      have hu := (Nat.le_div_iff_mul_le hp0).mpr (he'.symm ▸ (mem_Icc.mp hi).2)
      exact mem_image.mpr ⟨a, mem_filter.mpr
        ⟨mem_Icc.mpr ⟨ha, hu⟩, he'.symm ▸ (mem_Icc.mp hi).1⟩, he'⟩
  let H := P.biUnion layer
  have hinterval (n : ℕ) (hn : n ∈ H) : m ≤ n ∧ n ≤ M := by
    obtain ⟨p, hp, hpn⟩ := mem_biUnion.mp hn
    exact mem_Icc.mp (mem_filter.mp hpn).1
  have homit (i : ℕ) (hi : i < k) : f i ∉ H := by
    intro hn
    obtain ⟨p, hp, hpn⟩ := mem_biUnion.mp hn
    exact habsent p hp i hi (mem_filter.mp hpn).2
  have hmass : (∑ n ∈ H, (1 : ℝ) / n) =
      ∑ p ∈ P, (1 : ℝ) / p * ∑ a ∈ cofactors p, (1 : ℝ) / a := by
    rw [show H = P.biUnion layer from rfl, sum_biUnion hdisjoint]
    apply sum_congr rfl
    intro p hp
    rw [← himage p hp, sum_image (fun a _ b _ he =>
      Nat.eq_of_mul_eq_mul_right (hP p hp).1.pos he), mul_sum]
    apply sum_congr rfl
    intro a ha
    push_cast
    rw [one_div_mul_one_div, mul_comm (p : ℝ)]
  have hratio := Erdos287.log_ratio_lower_bound_from_omissions k hk f hfirst hmono hsum H hinterval homit
  rw [hmass] at hratio
  exact hratio

