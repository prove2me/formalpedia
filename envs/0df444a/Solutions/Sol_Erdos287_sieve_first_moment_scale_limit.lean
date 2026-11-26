-- Prove2me | solution 1 for Erdos287.sieve_first_moment_scale_limit
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:08:32.85045+00:00
-- url     : https://prove2.me/submissions/9e226146-d6f0-4448-9d00-449450b38b7a

import Mathlib

set_option autoImplicit false

/-- The exponent and tuple-size restrictions in the 145-group sieve bound
force the upper bound on its normalized first moment below one. -/
theorem solution (δ θ σ T : ℝ)
    (hδ : 78 / 145 < δ) (hlevel : δ ≤ 7 / 13 - 3 * θ)
    (hσ : 0 ≤ σ) (hσθ : σ ≤ θ) (hT : 1 ≤ T) (hsize : T ≤ 10 ^ (959 : ℕ)) :
    θ < 1 / 5655 ∧ 2 * σ * Real.log (1 + T) < 1 := by
  have hθ : θ < 1 / 5655 := by linarith
  refine ⟨hθ, ?_⟩
  have hlog10 : Real.log 10 < 5 / 2 := by
    have hlog := Real.log_lt_log (show 0 < (10 : ℝ) ^ (2 : ℕ) by positivity)
      (show (10 : ℝ) ^ (2 : ℕ) < 2 ^ (7 : ℕ) by norm_num)
    rw [Real.log_pow, Real.log_pow] at hlog
    norm_num at hlog
    linarith [Real.log_two_lt_d9]
  have hbig : 1 + T ≤ 2 * (10 : ℝ) ^ (959 : ℕ) := by
    calc
      1 + T ≤ T + T := by simpa [add_comm] using add_le_add_right hT T
      _ = 2 * T := by ring
      _ ≤ 2 * (10 : ℝ) ^ (959 : ℕ) := mul_le_mul_of_nonneg_left hsize (by norm_num)
  have hlog := Real.log_le_log (show 0 < 1 + T by linarith) hbig
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  norm_num at hlog
  have hlogT : Real.log (1 + T) ≤ 2400 := by
    linarith [Real.log_two_lt_d9]
  calc
    2 * σ * Real.log (1 + T) ≤ 2 * σ * 2400 :=
      mul_le_mul_of_nonneg_left hlogT (by positivity)
    _ < 1 := by linarith

