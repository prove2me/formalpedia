-- Prove2me | solution 1 for Erdos287.reflected_reciprocals_padic_expansion
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:52:14.354534+00:00
-- url     : https://prove2.me/submissions/f68dc571-d932-4953-94c7-7f52578d3fd0

import Mathlib

open Finset

set_option autoImplicit false

private theorem reflected_pair_remainder (x y : ℚ) (hy : 0 < y) (hxy : y < x) (r : ℕ) :
    (1 / (x - y) + 1 / (x + y)) + (2 * x / y ^ 2) *
      (∑ j ∈ range r, (x ^ 2 / y ^ 2) ^ j) =
      (2 * x ^ (2 * r + 1)) / ((x ^ 2 - y ^ 2) * y ^ (2 * r)) := by
  have hminus : x - y ≠ 0 := (sub_pos.mpr hxy).ne'
  have hplus : x + y ≠ 0 := (add_pos (hy.trans hxy) hy).ne'
  have hsquare : x ^ 2 - y ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_pow_left₀ hxy hy.le (by decide : (2 : ℕ) ≠ 0))).ne'
  let a := 2 * x / (x ^ 2 - y ^ 2)
  let z := x ^ 2 / y ^ 2
  have ha : 1 / (x - y) + 1 / (x + y) = a := by
    dsimp [a]
    field_simp [hminus, hplus, hsquare]
    ring
  have hz : a + 2 * x / y ^ 2 = a * z := by
    dsimp [a, z]
    field_simp [hy.ne', hsquare]
    ring
  have hsum (k : ℕ) : a + (2 * x / y ^ 2) * (∑ j ∈ range k, z ^ j) = a * z ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [sum_range_succ, mul_add, ← add_assoc, ih, pow_succ z k]
        calc
          a * z ^ k + 2 * x / y ^ 2 * z ^ k = (a + 2 * x / y ^ 2) * z ^ k := by ring
          _ = a * (z ^ k * z) := by rw [hz]; ring
  rw [ha, show x ^ 2 / y ^ 2 = z from rfl, hsum r]
  dsimp only [a, z]
  rw [div_pow, ← pow_mul, ← pow_mul, pow_succ x (2 * r)]
  field_simp [hy.ne', hsquare]

/-- The first `r` even inverse-power moments give a uniform p-adic
approximation to the reciprocal sum of all chosen reflected pairs. -/
theorem solution (T : Finset ℕ) (p c e r : ℕ) (hp : p.Prime)
    (he : 1 ≤ e) (hc : p ^ e ∣ c)
    (hT : ∀ d ∈ T, 0 < d ∧ d < c ∧ ¬ p ∣ d) :
    padicNorm p (∑ d ∈ T,
      (((1 : ℚ) / ((c : ℚ) - d) + (1 : ℚ) / ((c : ℚ) + d)) +
        ((2 : ℚ) * c / (d : ℚ) ^ 2) *
          (∑ j ∈ Finset.range r, ((c : ℚ) ^ 2 / (d : ℚ) ^ 2) ^ j))) ≤
      (p : ℚ) ^ (-(((2 * r + 1) * e : ℕ) : ℤ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpQ : (0 : ℚ) ≤ p := by positivity
  apply padicNorm.sum_le' _ (zpow_nonneg hpQ _)
  intro d hd
  obtain ⟨hdpos, hdc, hdu⟩ := hT d hd
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hdpos
  have hdcQ : (d : ℚ) < c := by exact_mod_cast hdc
  rw [reflected_pair_remainder (c : ℚ) (d : ℚ) hdQ hdcQ r]
  have hcp : p ∣ c := by
    have h := (pow_dvd_pow p he).trans hc
    simpa only [pow_one] using h
  have hcsq : p ∣ c ^ 2 := by rw [pow_two]; exact dvd_mul_of_dvd_left hcp c
  have hle : d ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (Nat.zero_le _) hdc.le 2
  have hbase : ¬ p ∣ c ^ 2 - d ^ 2 := by
    intro h
    have hsum : p ∣ (c ^ 2 - d ^ 2) + d ^ 2 := by rwa [Nat.sub_add_cancel hle]
    exact hdu (hp.dvd_of_dvd_pow ((Nat.dvd_add_right h).mp hsum))
  let den := (c ^ 2 - d ^ 2) * d ^ (2 * r)
  let num := 2 * c ^ (2 * r + 1)
  have hden : ¬ p ∣ den := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hbase h
    · exact hdu (hp.dvd_of_dvd_pow h)
  have hnum : p ^ ((2 * r + 1) * e) ∣ num := by
    have hpower := pow_dvd_pow_of_dvd hc (2 * r + 1)
    rw [← pow_mul, Nat.mul_comm e (2 * r + 1)] at hpower
    exact dvd_mul_of_dvd_right hpower 2
  have hcast : (num : ℚ) / den =
      2 * (c : ℚ) ^ (2 * r + 1) / (((c : ℚ) ^ 2 - (d : ℚ) ^ 2) * (d : ℚ) ^ (2 * r)) := by
    dsimp [num, den]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hle, Nat.cast_ofNat]
  rw [← hcast, padicNorm.div, (padicNorm.nat_eq_one_iff den).mpr hden, div_one]
  have hnumZ : ((p ^ ((2 * r + 1) * e) : ℕ) : ℤ) ∣ (num : ℤ) := by exact_mod_cast hnum
  simpa only [Int.cast_natCast] using (padicNorm.dvd_iff_norm_le (p := p)).mp hnumZ

