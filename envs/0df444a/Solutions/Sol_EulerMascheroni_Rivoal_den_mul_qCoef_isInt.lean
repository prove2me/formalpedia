-- Prove2me | solution 1 for EulerMascheroni.Rivoal.den_mul_qCoef_isInt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:18:18.02124+00:00
-- url     : https://prove2.me/submissions/544d7694-27ac-4d3e-91b6-9326f0417204

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.LinearCombination

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


theorem dvd_den (n i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 3 * n) : i ∣ den n := by
  have : i - 1 ∈ Finset.range (3 * n) := by simp; omega
  have h := Finset.dvd_lcm (f := fun i => i + 1) this
  rwa [show i - 1 + 1 = i by omega] at h

theorem den_mul_harmonic (n k : ℕ) (hk : k ≤ 3 * n) : ∃ z : ℤ, (den n : ℚ) * harmonic k = z := by
  have e : ∀ i ∈ Finset.range k, (den n : ℚ) * ((↑(i + 1) : ℚ))⁻¹
      = (((den n / (i + 1) : ℕ) : ℤ) : ℚ) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [Int.cast_natCast, Nat.cast_div (dvd_den n (i + 1) (by omega) (by omega)) (by positivity)]
    rfl
  refine ⟨∑ i ∈ Finset.range k, ((den n / (i + 1) : ℕ) : ℤ), ?_⟩
  rw [harmonic, Finset.mul_sum, Finset.sum_congr rfl e, Int.cast_sum]

theorem den_mul_hcoef (n j : ℕ) (hj : j ≤ n) : ∃ z : ℤ, (den n : ℚ) * hcoef n j = z := by
  obtain ⟨a, ha⟩ := den_mul_harmonic n (3 * n - j) (by omega)
  obtain ⟨b, hb⟩ := den_mul_harmonic n j (by omega)
  obtain ⟨c, hc⟩ := den_mul_harmonic n (n - j) (by omega)
  refine ⟨a + 2 * b - 2 * c, ?_⟩
  rw [hcoef]; push_cast
  linear_combination ha + 2 * hb - 2 * hc

end RivoalEasy

open EulerMascheroni.Rivoal in
theorem solution (n : ℕ) :
    ∃ z : ℤ, (EulerMascheroni.Rivoal.den n : ℚ) * EulerMascheroni.Rivoal.qCoef n = z := by
  have key : ∀ j ∈ Finset.range (n + 1), ∃ z : ℤ, (den n : ℚ) * (beta n j * hcoef n j) = z := by
    intro j hj
    simp at hj
    obtain ⟨z, hz⟩ := RivoalEasy.den_mul_hcoef n j (by omega)
    refine ⟨(RivoalEasy.bnat n j : ℤ) * z, ?_⟩
    rw [RivoalEasy.beta_eq n j (by omega)]; push_cast
    rw [← hz]; ring
  choose! f hf using key
  refine ⟨-∑ j ∈ Finset.range (n + 1), f j, ?_⟩
  rw [qCoef, mul_neg, Finset.mul_sum]; push_cast
  rw [Finset.sum_congr rfl hf]
