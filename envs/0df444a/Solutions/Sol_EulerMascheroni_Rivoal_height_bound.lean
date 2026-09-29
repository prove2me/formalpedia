-- Prove2me | solution 1 for EulerMascheroni.Rivoal.height_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:19:20.283063+00:00
-- url     : https://prove2.me/submissions/82582fa3-b246-4be3-b1df-04c5f8cbb2e6

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

namespace RivoalEasy
open EulerMascheroni.Rivoal

/-- natural-number version of `β`. -/
def bnat (n j : ℕ) : ℕ := (3 * n - j).factorial / (j.factorial * (n - j).factorial) ^ 2

theorem sq_dvd (n j : ℕ) (hj : j ≤ n) :
    (j.factorial * (n - j).factorial) ^ 2 ∣ (3 * n - j).factorial := by
  obtain ⟨b, rfl⟩ : ∃ b, n = j + b := ⟨n - j, by omega⟩
  have e1 : j + b - j = b := by omega
  have e2 : 3 * (j + b) - j = (j + b) + (j + 2 * b) := by omega
  rw [e1, e2]
  have h1 : j.factorial * b.factorial ∣ (j + b).factorial := Nat.factorial_mul_factorial_dvd_factorial_add j b
  have h2 : b.factorial * (j + b).factorial ∣ (j + 2 * b).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add b (j + b)
    rwa [show b + (j + b) = j + 2 * b by ring] at this
  have h3 := Nat.factorial_mul_factorial_dvd_factorial_add (j + b) (j + 2 * b)
  calc (j.factorial * b.factorial) ^ 2 ∣ (j + b).factorial * (j + b).factorial := by
        rw [sq]; exact Nat.mul_dvd_mul h1 h1
    _ ∣ (j + b).factorial * (b.factorial * (j + b).factorial) :=
        Nat.mul_dvd_mul_left _ (Dvd.intro_left _ rfl)
    _ ∣ (j + b).factorial * (j + 2 * b).factorial := Nat.mul_dvd_mul_left _ h2
    _ ∣ _ := h3

theorem bnat_mul (n j : ℕ) (hj : j ≤ n) :
    bnat n j * (j.factorial * (n - j).factorial) ^ 2 = (3 * n - j).factorial :=
  Nat.div_mul_cancel (sq_dvd n j hj)

theorem beta_eq (n j : ℕ) (hj : j ≤ n) : beta n j = (bnat n j : ℚ) := by
  have hpos : ((j.factorial : ℚ) * ((n - j).factorial : ℚ)) ^ 2 ≠ 0 := by positivity
  rw [beta, div_eq_iff hpos]
  have := congrArg (fun x : ℕ => (x : ℚ)) (bnat_mul n j hj)
  push_cast at this
  exact this.symm

theorem rCoef_eq (n : ℕ) : rCoef n = ((∑ j ∈ Finset.range (n + 1), bnat n j : ℕ) : ℚ) := by
  rw [rCoef]; push_cast
  exact Finset.sum_congr rfl fun j hj => beta_eq n j (by simp at hj; omega)


theorem choose3_le (n : ℕ) : (3 * n).choose n * 4 ^ n ≤ 27 ^ n := by
  have h := (add_pow (1 : ℕ) 2 (3 * n)).symm
  simp only [Nat.cast_id] at h
  have hs : (3 * n).choose n * 4 ^ n ≤ ∑ k ∈ Finset.range (3 * n + 1), 1 ^ k * 2 ^ (3 * n - k) * (3 * n).choose k := by
    have := Finset.single_le_sum (f := fun k => 1 ^ k * 2 ^ (3 * n - k) * (3 * n).choose k)
      (fun _ _ => Nat.zero_le _) (show n ∈ Finset.range (3 * n + 1) by simp; omega)
    refine le_trans (le_of_eq ?_) this
    simp only [one_pow, one_mul]
    rw [show 3 * n - n = 2 * n by omega, pow_mul]; ring
  rw [h] at hs
  simpa [pow_mul] using hs

theorem fact3_le (n : ℕ) : (3 * n).factorial ≤ 27 ^ n * n.factorial ^ 3 := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  have e2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 3 * n - n = 2 * n by omega] at e1
  rw [show 2 * n - n = n by omega] at e2
  have c2 : (2 * n).choose n ≤ 4 ^ n := by
    have := Nat.choose_le_two_pow (2 * n) n
    rwa [pow_mul] at this
  have hc : (3 * n).choose n * (2 * n).choose n ≤ 27 ^ n :=
    le_trans (Nat.mul_le_mul_left _ c2) (choose3_le n)
  rw [← e1, ← e2]
  calc (3 * n).choose n * n.factorial * ((2 * n).choose n * n.factorial * n.factorial)
      = ((3 * n).choose n * (2 * n).choose n) * n.factorial ^ 3 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hc

theorem bnat_le (n j : ℕ) (hj : j ≤ n) :
    bnat n j ≤ n.choose j ^ 2 * 27 ^ n * n.factorial := by
  have hD : 0 < (j.factorial * (n - j).factorial) ^ 2 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hD
  rw [bnat_mul n j hj]
  have e := Nat.choose_mul_factorial_mul_factorial hj
  calc (3 * n - j).factorial ≤ (3 * n).factorial := Nat.factorial_le (by omega)
    _ ≤ 27 ^ n * n.factorial ^ 3 := fact3_le n
    _ = _ := by rw [← e]; ring

theorem sum_bnat_le (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), bnat n j ≤ 108 ^ n * n.factorial := by
  calc ∑ j ∈ Finset.range (n + 1), bnat n j
      ≤ ∑ j ∈ Finset.range (n + 1), n.choose j * 2 ^ n * 27 ^ n * n.factorial := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp at hj
        refine le_trans (bnat_le n j (by omega)) ?_
        rw [sq]
        gcongr
        exact Nat.choose_le_two_pow n j
    _ = (∑ j ∈ Finset.range (n + 1), n.choose j) * 2 ^ n * 27 ^ n * n.factorial := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ = 108 ^ n * n.factorial := by
        rw [Nat.sum_range_choose, show (108 : ℕ) = 2 * 2 * 27 by norm_num, mul_pow, mul_pow]

theorem harmonic_nonneg' (k : ℕ) : 0 ≤ harmonic k := by
  rw [harmonic]; exact Finset.sum_nonneg fun i _ => by positivity

theorem harmonic_le_self (k : ℕ) : harmonic k ≤ k := by
  rw [harmonic]
  calc ∑ i ∈ Finset.range k, ((↑(i + 1) : ℚ))⁻¹ ≤ ∑ i ∈ Finset.range k, (1 : ℚ) :=
        Finset.sum_le_sum fun i _ => inv_le_one_of_one_le₀ (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℚ) ≤ i)])
    _ = k := by simp

theorem abs_hcoef_le (n j : ℕ) (hj : j ≤ n) : |hcoef n j| ≤ 9 * n := by
  rw [hcoef, abs_le]
  have a1 := harmonic_nonneg' (3 * n - j)
  have a2 := harmonic_nonneg' j
  have a3 := harmonic_nonneg' (n - j)
  have b1 := harmonic_le_self (3 * n - j)
  have b2 := harmonic_le_self j
  have b3 := harmonic_le_self (n - j)
  have c1 : ((3 * n - j : ℕ) : ℚ) ≤ 3 * n := by
    have : 3 * n - j ≤ 3 * n := by omega
    exact_mod_cast this
  have c2 : (j : ℚ) ≤ n := by exact_mod_cast hj
  have c3 : ((n - j : ℕ) : ℚ) ≤ n := by
    have : n - j ≤ n := by omega
    exact_mod_cast this
  constructor <;> linarith

end RivoalEasy

open EulerMascheroni.Rivoal in
theorem solution (n : ℕ) :
    |EulerMascheroni.Rivoal.qCoef n| + |EulerMascheroni.Rivoal.rCoef n|
      ≤ (9 * n + 1) * 108 ^ n * (n.factorial : ℚ) := by
  have hr : rCoef n ≤ 108 ^ n * n.factorial := by
    rw [RivoalEasy.rCoef_eq]; exact_mod_cast RivoalEasy.sum_bnat_le n
  have hr0 : 0 ≤ rCoef n := by rw [RivoalEasy.rCoef_eq]; positivity
  have hq : |qCoef n| ≤ 9 * n * rCoef n := by
    rw [qCoef, abs_neg, rCoef, Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
    simp at hj
    have hb : 0 ≤ beta n j := by rw [RivoalEasy.beta_eq n j (by omega)]; positivity
    rw [abs_mul, abs_of_nonneg hb, mul_comm]
    exact mul_le_mul_of_nonneg_right (RivoalEasy.abs_hcoef_le n j (by omega)) hb
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  rw [abs_of_nonneg hr0]
  calc |qCoef n| + rCoef n ≤ (9 * n + 1) * rCoef n := by linarith
    _ ≤ (9 * n + 1) * (108 ^ n * n.factorial) := by gcongr
    _ = _ := by ring
