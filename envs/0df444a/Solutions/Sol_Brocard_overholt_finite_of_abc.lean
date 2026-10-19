-- Prove2me | solution 1 for Brocard.overholt_finite_of_abc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T07:49:54.48535+00:00
-- url     : https://prove2.me/submissions/4c391c9d-dad6-4112-b334-ff630d9237c5

import Mathlib
import Definitions.Def_Brocard_Defs

namespace BRAux
open Brocard Filter Topology

lemma rad_mul_le (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : radical (x * y) ≤ radical x * radical y := by
  classical
  unfold radical
  rw [Nat.primeFactors_mul hx hy]
  have h := Finset.prod_union_inter (s₁ := x.primeFactors) (s₂ := y.primeFactors) (f := fun p => p)
  have hpos : 0 < ∏ p ∈ x.primeFactors ∩ y.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos
  have h1 : (∏ p ∈ x.primeFactors ∪ y.primeFactors, p) * 1 ≤
      (∏ p ∈ x.primeFactors ∪ y.primeFactors, p) * ∏ p ∈ x.primeFactors ∩ y.primeFactors, p :=
    Nat.mul_le_mul_left _ hpos
  rw [h, mul_one] at h1
  exact h1

lemma rad_le_self (m : ℕ) (hm : m ≠ 0) : radical m ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

lemma rad_factorial_le (n : ℕ) (hn : n ≠ 0) : radical n.factorial ≤ 4 ^ n := by
  classical
  have hsub : n.factorial.primeFactors ⊆ Nat.primesLE n := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp'.1).mp hp'.2.1, hp'.1⟩
  have h1 : radical n.factorial ≤ primorial n := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
      (Nat.prime_of_mem_primesLE hp).one_lt.le
  exact h1.trans (primorial_lt_four_pow n hn).le

lemma rad_le (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    radical (1 * n.factorial * m ^ 2) ≤ 4 ^ n * m := by
  rw [one_mul]
  have h1 := rad_mul_le n.factorial (m ^ 2) (Nat.factorial_ne_zero n) (pow_ne_zero 2 hm)
  have h2 : radical (m ^ 2) = radical m := by
    unfold radical; rw [Nat.primeFactors_pow m two_ne_zero]
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul (rad_factorial_le n hn) (rad_le_self m hm))

theorem main (habc : ABCConjecture) :
    {p : ℕ × ℕ | Nat.factorial p.1 + 1 = p.2 ^ 2}.Finite := by
  obtain ⟨K, hK0, hK⟩ := habc (1 / 2) (by norm_num)
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop (4096 : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, (4096 : ℝ) ^ n / n.factorial < 1 / K ^ 4 :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hev
  refine (Set.finite_Iio (n0 + 1)).prod (Set.finite_Iic ((n0 + 1).factorial + 1)) |>.subset ?_
  rintro ⟨n, m⟩ hnm
  simp only [Set.mem_ofPred_eq] at hnm
  have hm0 : m ≠ 0 := by
    rintro rfl; simp at hnm
  have hnlt : n < n0 + 1 := by
    by_contra hge
    push Not at hge
    have hn : n ≠ 0 := by omega
    have hn' := hn0 n (by omega)
    have habc' := hK 1 n.factorial (m ^ 2) one_pos (Nat.factorial_pos n)
      (Nat.coprime_one_left _) (by rw [← hnm]; ring)
    have hr := rad_le n m hn hm0
    have hr' : ((radical (1 * n.factorial * m ^ 2) : ℕ) : ℝ) ≤ (4 : ℝ) ^ n * m := by
      exact_mod_cast hr
    have hmr : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have h3 : ((m ^ 2 : ℕ) : ℝ) < K * ((4 : ℝ) ^ n * m) ^ (1 + 1 / 2 : ℝ) :=
      habc'.trans_le (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hr' (by norm_num)) hK0.le)
    set r : ℝ := (4 : ℝ) ^ n * m with hr_def
    have hr0 : 0 < r := by positivity
    have hsq : (r ^ (1 + 1 / 2 : ℝ)) ^ 2 = r ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; norm_num
    have h4 : ((m : ℝ) ^ 2) ^ 2 < (K * r ^ (1 + 1 / 2 : ℝ)) ^ 2 := by
      push_cast at h3
      exact pow_lt_pow_left₀ h3 (by positivity) two_ne_zero
    rw [mul_pow, hsq, hr_def] at h4
    have h5 : (m : ℝ) < K ^ 2 * 64 ^ n := by
      have e : ((m : ℝ) ^ 2) ^ 2 = m * m ^ 3 := by ring
      have e2 : K ^ 2 * ((4 : ℝ) ^ n * m) ^ 3 = K ^ 2 * 64 ^ n * m ^ 3 := by
        rw [mul_pow, ← pow_mul, mul_comm n 3, pow_mul]; norm_num; ring
      rw [e, e2] at h4
      exact lt_of_mul_lt_mul_right h4 (by positivity)
    have h6 : (n.factorial : ℝ) < K ^ 4 * 4096 ^ n := by
      have : ((n.factorial + 1 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by exact_mod_cast hnm
      push_cast at this
      have h7 : (m : ℝ) ^ 2 < (K ^ 2 * 64 ^ n) ^ 2 := pow_lt_pow_left₀ h5 hmr.le two_ne_zero
      have e3 : (K ^ 2 * (64 : ℝ) ^ n) ^ 2 = K ^ 4 * 4096 ^ n := by
        have : (4096 : ℝ) ^ n = ((64 : ℝ) ^ n) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; ring
      linarith
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_lt_div_iff₀ hf (by positivity), one_mul] at hn'
    nlinarith
  refine ⟨hnlt, ?_⟩
  have hm2 : m ≤ m ^ 2 := by nlinarith [Nat.pos_of_ne_zero hm0]
  have : n.factorial ≤ (n0 + 1).factorial := Nat.factorial_le (by omega)
  show m ≤ (n0 + 1).factorial + 1
  omega

end BRAux

theorem solution (habc : Brocard.ABCConjecture) :
    {p : ℕ × ℕ | Nat.factorial p.1 + 1 = p.2 ^ 2}.Finite :=
  BRAux.main habc
