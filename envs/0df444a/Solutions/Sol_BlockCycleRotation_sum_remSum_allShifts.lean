-- Prove2me | solution 1 for BlockCycleRotation.sum_remSum_allShifts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:05:50.819559+00:00
-- url     : https://prove2.me/submissions/3aa781c2-bf9f-42d5-b320-7edd5e3918da

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_remSum_mul
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
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
/-- The remainder sums, aggregated over the gcd. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = ∑ g ∈ n.divisors, g * ∑ k' ∈ shifts (n / g), remSum (n / g) k':= by
  rw [show (∑ g ∈ n.divisors, g * ∑ k' ∈ shifts (n / g), remSum (n / g) k')
      = ∑ g ∈ n.divisors, ∑ k' ∈ shifts (n / g), g * remSum (n / g) k' from
    Finset.sum_congr rfl fun g _ => Finset.mul_sum _ _ _]
  rw [← sum_allShifts_eq hn (fun g k' => g * remSum (n / g) k')]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : Nat.gcd n k * (n / Nat.gcd n k) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n k)
  have h2 : Nat.gcd n k * (k / Nat.gcd n k) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)
  have hm := remSum_mul (k / Nat.gcd n k) (n / Nat.gcd n k) (Nat.gcd n k)
  rw [h1, h2] at hm
  exact hm
