-- Prove2me | solution 1 for DeletedPrimes.term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:24.264807+00:00
-- url     : https://prove2.me/submissions/9661de1e-15dc-4063-bf4b-c3219423530e

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) {p j : ℕ} (h1 : 2 ^ j ≤ p) (h2 : p < 2 * 2 ^ j) :
    Real.log p / (p : ℝ) ^ α ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α := by
  have h1' : (2 : ℝ) ^ j ≤ p := by exact_mod_cast h1
  have h2' : (p : ℝ) ≤ 2 ^ (j + 1) := by rw [pow_succ']; exact_mod_cast h2.le
  have hp : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) h1'
  apply div_le_div₀ (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))) _ (by positivity)
    (Real.rpow_le_rpow (by positivity) h1' hα)
  calc Real.log p ≤ Real.log (2 ^ (j + 1)) := Real.log_le_log hp h2'
    _ = ((j : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
end DeletedPrimes
