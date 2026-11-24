-- Prove2me | solution 1 for Formalism.LogFactorialBounds.sum_primesLE_log_div_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:51.165564+00:00
-- url     : https://prove2.me/submissions/f7934a5c-8f97-4c55-81f5-9fdc361a6bb7

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Theorems.Thm_Formalism_LogFactorialBounds_sum_div_mul_log_le_log_factorial
import Theorems.Thm_Formalism_LogFactorialBounds_log_factorial_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LogFactorialBounds
open Finset Real
namespace Formalism.LogFactorialBounds
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hprim : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    have h4 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_4_pow n
    have hpos : (0 : ℝ) < (primorial n : ℕ) := by exact_mod_cast primorial_pos n
    have hlog : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p := by
      unfold primorial
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr _ (fun _ _ => rfl)
        ext p
        simp [Nat.mem_primesLE, Nat.lt_succ_iff, and_comm]
      · intro p hp
        have := (Finset.mem_filter.1 hp).2.pos
        exact_mod_cast this.ne'
    rw [← hlog, ← Real.log_pow]
    exact Real.log_le_log hpos h4
  have hterm : ∀ p ∈ Nat.primesLE n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have h3 : n < n / p * p + p := Nat.lt_div_mul_add hpp.pos
      have h4 : (n : ℝ) ≤ ((n / p * p + p : ℕ) : ℝ) := by exact_mod_cast h3.le
      push_cast at h4
      linarith
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hdiv hlogp
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
      ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ Nat.primesLE n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hterm
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
          + ∑ p ∈ Nat.primesLE n, Real.log p := Finset.sum_add_distrib
      _ ≤ Real.log (n.factorial : ℕ) + n * Real.log 4 :=
          add_le_add (sum_div_mul_log_le_log_factorial n) hprim
      _ ≤ n * (Real.log n + Real.log 4) := by
          have := log_factorial_le n
          nlinarith
  exact le_of_mul_le_mul_left hsum hnpos
end Formalism.LogFactorialBounds
