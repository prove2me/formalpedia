-- Prove2me | solution 1 for BitcoinSelfishErgodic.dist_zero
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:48:50.823856+00:00
-- url     : https://prove2.me/submissions/f4cdc714-e210-4121-8f21-80c21dbe23f7

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

/-- One step from `μ`, mass at `zero`: from `zero` (honest block), from the tie (every outcome)
and from lead `2` (honest block). -/
theorem solution (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ .zero = (1 - α) * μ .zero + μ .tie + (1 - α) * μ (.lead 1) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_single 1 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · simp [P, outcomeSum, step]
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]
