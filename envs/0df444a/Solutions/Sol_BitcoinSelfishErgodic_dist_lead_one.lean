-- Prove2me | solution 1 for BitcoinSelfishErgodic.dist_lead_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:48:52.906381+00:00
-- url     : https://prove2.me/submissions/7e20d2bb-3252-4caf-aa97-8fd26ada9c85

import Definitions.Def_BitcoinSelfishErgodic
import Theorems.Thm_BitcoinSelfishMining_stationary_balance
import Theorems.Thm_BitcoinSelfishMining_total_mass
import Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
import Theorems.Thm_BitcoinSelfishMining_threshold
import Theorems.Thm_BitcoinSelfishUnique_stationary_unique

open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

private theorem one_sub_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - α := by linarith

private theorem ratio_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < α / (1 - α) :=
  div_pos h0 (one_sub_pos h1)

private theorem ratio_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  (ratio_pos h0 h1).le

private theorem ratio_lt_one {α : ℝ} (h1 : α < 1 / 2) : α / (1 - α) < 1 :=
  (div_lt_one (one_sub_pos h1)).mpr (by linarith)

/-- `α r^m + (1 - α) r^(m+2) = r^(m+1)` for `r = α / (1 - α)`. -/
private theorem ratio_step {α : ℝ} (h1 : α < 1 / 2) (m : ℕ) :
    α * (α / (1 - α)) ^ m + (1 - α) * (α / (1 - α)) ^ (m + 2) = (α / (1 - α)) ^ (m + 1) := by
  have h1' := (one_sub_pos h1).ne'
  have e : (1 - α) * (α / (1 - α)) = α := mul_div_cancel₀ _ h1'
  linear_combination ((α / (1 - α)) ^ (m + 1) - (α / (1 - α)) ^ m) * e

/-- One step from `μ`, mass at lead `2`: from lead `1` (pool block) and lead `3` (honest block). -/
theorem solution (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead 1) = α * μ (.lead 0) + (1 - α) * μ (.lead 2) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_sum (s := {0, 2}) ?_, Finset.sum_pair (by norm_num)]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rcases b with _ | _ | b
    · exact absurd rfl hb.1
    · simp [P, outcomeSum, step]
    · have : b ≠ 0 := by omega
      simp [P, outcomeSum, step, this]
