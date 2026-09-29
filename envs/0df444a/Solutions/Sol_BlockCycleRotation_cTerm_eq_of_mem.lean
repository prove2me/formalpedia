-- Prove2me | solution 1 for BlockCycleRotation.cTerm_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:28:04.509504+00:00
-- url     : https://prove2.me/submissions/e9650752-d401-4ad7-ae25-06438000ab83

import Definitions.Def_BlockCycleRotation_Constant
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

/-- **The summand identity.**  `1/(a²(a+a')) - a'/(2a²(a+a')²) = (2a+a')/(2a²(a+a')²)`. -/
theorem cTerm_summand_eq {a a' : ℝ} (ha : a ≠ 0) (haa : a + a' ≠ 0) :
    1 / (a ^ 2 * (a + a')) - a' / (2 * a ^ 2 * (a + a') ^ 2)
      = (2 * a + a') / (2 * a ^ 2 * (a + a') ^ 2) := by
  field_simp
  ring

end BlockCycleRotation

open BlockCycleRotation in
/-- The value of `cTerm` on an admissible pair, in the paper's split form. -/
theorem solution {a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    cTerm (a, a')
      = 1 / ((a : ℝ) ^ 2 * ((a : ℝ) + a')) - (a' : ℝ) / (2 * (a : ℝ) ^ 2 * ((a : ℝ) + a') ^ 2):= by
  have ha : (a : ℝ) ≠ 0 := by
    have : 0 < a := by omega
    positivity
  have haa : (a : ℝ) + (a' : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by
      have : 0 < a := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    positivity
  rw [cTerm_summand_eq ha haa]
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
