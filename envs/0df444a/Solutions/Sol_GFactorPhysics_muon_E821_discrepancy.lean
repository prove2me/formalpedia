-- Prove2me | solution 1 for GFactorPhysics.muon_E821_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:39.45499+00:00
-- url     : https://prove2.me/submissions/bdb8cbf4-485a-41b9-9a61-29b012d28511

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution :
    (3.4 : ℝ) ≤ |(-2.0023318416 : ℝ) - (-2.00233183620)| /
        Real.sqrt ((1.3e-9 : ℝ) ^ 2 + (8.6e-10 : ℝ) ^ 2) ∧
      |(-2.0023318416 : ℝ) - (-2.00233183620)| /
        Real.sqrt ((1.3e-9 : ℝ) ^ 2 + (8.6e-10 : ℝ) ^ 2) < 3.5 := by
  let desvio : ℝ := Real.sqrt ((1.3e-9 : ℝ) ^ 2 + (8.6e-10 : ℝ) ^ 2)
  have positivo : 0 < desvio := Real.sqrt_pos.2 (by norm_num)
  have superior : desvio < 1.559e-9 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.559e-9)).2
    norm_num
  have inferior : (1.558e-9 : ℝ) < desvio := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  change (3.4 : ℝ) ≤ |(-2.0023318416 : ℝ) - (-2.00233183620)| / desvio ∧
    |(-2.0023318416 : ℝ) - (-2.00233183620)| / desvio < 3.5
  constructor
  · apply (le_div_iff₀ positivo).2
    norm_num
    linarith
  · apply (div_lt_iff₀ positivo).2
    norm_num
    linarith
