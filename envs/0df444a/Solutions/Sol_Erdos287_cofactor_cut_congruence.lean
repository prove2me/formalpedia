-- Prove2me | solution 1 for Erdos287.cofactor_cut_congruence
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:04:53.290156+00:00
-- url     : https://prove2.me/submissions/4b8ea54a-09de-4519-afeb-a53b1b493928

import Mathlib

open Finset

set_option autoImplicit false

private theorem norm_reciprocal {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    padicNorm p ((1 : ℚ) / n) = (p : ℚ) ^ (padicValNat p n : ℤ) := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hnQ), padicValRat.inv,
    padicValRat.of_nat, neg_neg]

private theorem norm_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    padicNorm p ((p : ℚ) ^ e) = (p : ℚ) ^ (-(e : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p hp.one_lt, pow_succ]

/-- Clearing the reciprocal cofactors above a prime-power cut leaves at
least one additional power of the prime in the numerator. -/
theorem solution (D : Finset ℕ) (p e L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hpos : ∀ n ∈ D, 0 < n) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hL : ∀ n ∈ D, p ^ e ∣ n → n / (p ^ e) ∣ L) (hLp : p ^ j ∣ L) :
    p ^ (j + 1) ∣ ∑ n ∈ D.filter (fun n => p ^ e ∣ n), L / (n / (p ^ e)) := by
  have : Fact p.Prime := ⟨hp⟩
  let q := p ^ e
  let H := D.filter (fun n => q ∣ n)
  let T := D.filter (fun n => ¬ q ∣ n)
  let U : ℚ := ∑ n ∈ H, (1 : ℚ) / n
  let V : ℚ := ∑ n ∈ T, (1 : ℚ) / n
  let A : ℕ := ∑ n ∈ H, L / (n / q)
  change p ^ (j + 1) ∣ A
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpone : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hsplit : U + V = 1 :=
    (sum_filter_add_sum_filter_not D (fun n => q ∣ n) (fun n => (1 : ℚ) / n)).trans hsum
  have hV : padicNorm p V ≤ (p : ℚ) ^ ((e - 1 : ℕ) : ℤ) := by
    apply padicNorm.sum_le' _ (zpow_nonneg hpQ.le _)
    intro n hn
    obtain ⟨hnD, hnd⟩ := mem_filter.mp hn
    have hnpos := hpos n hnD
    have hev : padicValNat p n < e :=
      lt_of_not_ge fun hv => hnd ((padicValNat_dvd_iff_le hnpos.ne').mpr hv)
    rw [norm_reciprocal hnpos.ne']
    exact zpow_le_zpow_right₀ hpone (by exact_mod_cast (show padicValNat p n ≤ e - 1 by omega))
  have hU : padicNorm p U ≤ (p : ℚ) ^ ((e - 1 : ℕ) : ℤ) := by
    rw [eq_sub_of_add_eq hsplit]
    apply padicNorm.sub.trans
    rw [padicNorm.one]
    exact max_le (by rw [← zpow_zero (p : ℚ)]; exact zpow_le_zpow_right₀ hpone (by positivity)) hV
  have hA : (A : ℚ) = L * (((p : ℚ) ^ e) * U) := by
    simp only [A, U, Nat.cast_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    obtain ⟨hnD, hnd⟩ := mem_filter.mp hn
    have hnpos := hpos n hnD
    have hcast : ((n / q : ℕ) : ℚ) * (p : ℚ) ^ e = n := by exact_mod_cast Nat.div_mul_cancel hnd
    have hcoe : ((L / (n / q) : ℕ) : ℚ) * (n / q : ℕ) = L := by
      exact_mod_cast Nat.div_mul_cancel (hL n hnD hnd)
    rw [mul_one_div, ← mul_div_assoc]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hnpos.ne')).mpr
    calc
      ((L / (n / q) : ℕ) : ℚ) * n =
        (((L / (n / q) : ℕ) : ℚ) * (n / q : ℕ)) * (p : ℚ) ^ e := by rw [mul_assoc, hcast]
      _ = _ := by rw [hcoe]
  have hLNorm : padicNorm p (L : ℚ) ≤ (p : ℚ) ^ (-(j : ℤ)) := by
    have hd : (p : ℤ) ^ j ∣ (L : ℤ) := by exact_mod_cast hLp
    simpa only [Int.cast_natCast] using
      (padicNorm.dvd_iff_norm_le (p := p) (n := j) (z := (L : ℤ))).mp hd
  rw [← Int.natCast_dvd_natCast, padicNorm.dvd_iff_norm_le, Int.cast_natCast, hA,
    padicNorm.mul, padicNorm.mul, norm_prime_pow hp]
  calc
    _ ≤ (p : ℚ) ^ (-(j : ℤ)) * ((p : ℚ) ^ (-(e : ℤ)) * (p : ℚ) ^ ((e - 1 : ℕ) : ℤ)) :=
      mul_le_mul hLNorm (mul_le_mul_of_nonneg_left hU (by positivity))
        (mul_nonneg (zpow_nonneg hpQ.le _) (padicNorm.nonneg _)) (zpow_nonneg hpQ.le _)
    _ = (p : ℚ) ^ (-((j + 1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hpQ.ne', ← zpow_add₀ hpQ.ne']
      congr 1
      omega

