-- Prove2me | solution 1 for BlockCycleRotation.error_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:23:10.44149+00:00
-- url     : https://prove2.me/submissions/45fd46c6-46c9-44b9-abff-6e4c47b619d2

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
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
/-- **The three layers combined: `O(n^{3/2+ε})`.**

The aggregate of the per-pair error bounds, summed over pairs and divisors, is
`O(n^{3/2+ε})` — the bound Lemmas 18 and 19 of the paper establish for
`G₂ + G₃`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)))
        ≤ C * (n : ℝ) ^ (3 / 2 + ε):= by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le (half_pos hε)
  refine ⟨12 * C0 * (1 + 2 / ε), by positivity, fun n hn => ?_⟩
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hhalf : (0 : ℝ) < ε / 2 := half_pos hε
  -- `√n ≤ n^{1/2}`
  have hsqrt : ((Nat.sqrt n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
      have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by
        have h2 := Nat.sqrt_le' n
        rwa [pow_two] at h2
      have hcast : ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hsq
      nlinarith [hcast]
    have h2 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hn'
    rw [Real.sqrt_eq_rpow] at h1 h2
    linarith
  -- `1 + log n ≤ (1 + 2/ε)·n^{ε/2}`
  have hlogb : 1 + Real.log n ≤ (1 + 2 / ε) * (n : ℝ) ^ (ε / 2) := by
    have h := Real.log_le_rpow_div hnpos.le hhalf
    have hge : (1 : ℝ) ≤ (n : ℝ) ^ (ε / 2) := Real.one_le_rpow hn' hhalf.le
    have hdiv : (n : ℝ) ^ (ε / 2) / (ε / 2) = (2 / ε) * (n : ℝ) ^ (ε / 2) := by
      field_simp
    rw [hdiv] at h
    nlinarith
  have hd := hCd n hn.ne'
  have hdnn : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  have hrpow : (n : ℝ) ^ (3 / 2 + ε)
      = (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2))) := by
    rw [show ((n : ℝ) * (n : ℝ) ^ (ε / 2)) = (n : ℝ) ^ ((1 : ℝ) + ε / 2) from by
      rw [Real.rpow_add hnpos, Real.rpow_one]]
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hrpow]
  have hlognn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn'
  have hC : (3 * (n : ℝ) * (1 + Real.log n))
      ≤ 3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2)) :=
    mul_le_mul_of_nonneg_left hlogb (by positivity)
  have hBC : ((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))
      ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 2))
          * (3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2))) :=
    mul_le_mul hsqrt hC (by positivity) (by positivity)
  refine (mul_le_mul hd hBC (by positivity) (by positivity)).trans ?_
  have heq : (C0 * (n : ℝ) ^ (ε / 2))
        * ((2 * (n : ℝ) ^ ((1 : ℝ) / 2))
          * (3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2))))
      = 6 * C0 * (1 + 2 / ε)
          * ((n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2)))) := by
    ring
  rw [heq]
  have hpos : (0 : ℝ)
      ≤ (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2))) := by
    positivity
  have hfac : (0 : ℝ) ≤ C0 * (1 + 2 / ε) := by positivity
  nlinarith [mul_nonneg hfac hpos]
