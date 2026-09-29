-- Prove2me | solution 1 for BlockCycleRotation.outer_layer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:22:08.402949+00:00
-- url     : https://prove2.me/submissions/10e64a3e-36d7-49e2-85e1-cfaac079a698

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
/-- **The outer layer.** -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
          * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
      ≤ (n.divisors.card : ℝ)
          * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))):= by
  calc ∑ d ∈ n.divisors,
        ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
          * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
      ≤ ∑ _d ∈ n.divisors,
          (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
        have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
        have hmn : n / d ≤ n := Nat.div_le_self _ _
        have hm' : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm
        have hmn' : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        have hlognn : (0 : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) := Real.log_nonneg hm'
        have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by linarith) hmn'
        have hs : Nat.sqrt ((n / d - 1) / d) ≤ Nat.sqrt n := by
          refine Nat.sqrt_le_sqrt ?_
          calc (n / d - 1) / d ≤ n / d - 1 := Nat.div_le_self _ _
            _ ≤ n := by omega
        have h1 : ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1) ≤ ((Nat.sqrt n : ℝ) + 1) := by
          have hc : (Nat.sqrt ((n / d - 1) / d) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            exact_mod_cast hs
          linarith
        have h2 : (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
            ≤ (3 * (n : ℝ) * (1 + Real.log n)) := by nlinarith
        have hnn2 : (0 : ℝ) ≤ (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))) := by
          nlinarith
        exact mul_le_mul h1 h2 hnn2 (by positivity)
    _ = (n.divisors.card : ℝ)
          * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
