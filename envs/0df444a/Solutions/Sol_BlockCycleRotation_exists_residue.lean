-- Prove2me | solution 1 for BlockCycleRotation.exists_residue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:11:16.116789+00:00
-- url     : https://prove2.me/submissions/d3197848-0210-420b-a7db-c36f780ad48e

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- With `gcd(a,a') = 1`, the congruence `a ∣ m - a'·b'` is `b' ≡ c (mod a)` for
a residue `c` depending only on `a`, `a'` and `m`. -/
theorem solution {a a' m : ℕ} (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ b : ℤ, ((a : ℤ) ∣ ((m : ℤ) - a' * b)) ↔ ((a : ℤ) ∣ (b - c)):= by
  have hco : IsCoprime (a : ℤ) (a' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using hgcd
  obtain ⟨u, v, huv⟩ := id hco
  -- `u * a + v * a' = 1`, so `v * m` inverts `a'` against `m`
  refine ⟨v * m, fun b => ?_⟩
  have hkey : (m : ℤ) - a' * b = ((m : ℤ) - a' * (v * m)) - a' * (b - v * m) := by ring
  have hdvd1 : (a : ℤ) ∣ ((m : ℤ) - a' * (v * m)) := by
    refine ⟨u * m, ?_⟩
    have : (a' : ℤ) * (v * m) = (1 - u * a) * m := by
      rw [← huv]; ring
    rw [this]; ring
  constructor
  · intro h
    rw [hkey] at h
    have h2 : (a : ℤ) ∣ (a' : ℤ) * (b - v * m) := (dvd_sub_right hdvd1).1 h
    exact IsCoprime.dvd_of_dvd_mul_left hco h2
  · intro h
    rw [hkey]
    exact dvd_sub hdvd1 (Dvd.dvd.mul_left h _)
