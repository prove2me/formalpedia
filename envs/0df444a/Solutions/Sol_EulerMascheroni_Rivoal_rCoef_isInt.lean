-- Prove2me | solution 1 for EulerMascheroni.Rivoal.rCoef_isInt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:17:41.170992+00:00
-- url     : https://prove2.me/submissions/d60519d6-29ee-4180-8bd5-96e5f9bc1ae9

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.Data.Nat.Choose.Basic

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

end RivoalEasy

theorem solution (n : ℕ) :
    ∃ z : ℤ, EulerMascheroni.Rivoal.rCoef n = z :=
  ⟨_, by rw [RivoalEasy.rCoef_eq]; exact (Int.cast_natCast _).symm⟩
