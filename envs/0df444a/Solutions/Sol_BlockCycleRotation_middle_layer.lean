-- Prove2me | solution 1 for BlockCycleRotation.middle_layer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:21:55.692181+00:00
-- url     : https://prove2.me/submissions/9bb6d43f-f6fb-4d1a-9f23-268912bb77b2

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_card_a_le
import Theorems.Thm_BlockCycleRotation_middle_layer_bound
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
/-- **The middle layer, combined.**  The per-pair error bounds sum to
`O(√(m/d) · m · log m)` — which is `m^{3/2}/√d` up to the logarithm. -/
theorem solution {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)):= by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) ≤ 1 + Real.log m := by
    have := Real.log_nonneg hm'
    linarith
  refine (middle_layer_bound hm).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h := card_a_le (m := m) hd
  have : (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
      ≤ ((Nat.sqrt ((m - 1) / d) + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith
