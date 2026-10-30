-- Prove2me | solution 2 for BitcoinSelfishMining.balance_lead
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:25:44.412511+00:00
-- url     : https://prove2.me/submissions/aac4a490-9386-4419-ae53-c6c55e75a456

import Definitions.Def_BitcoinSelfishMining

open BitcoinSelfishMining

private theorem denom_pos_aux {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < denom α := by
  unfold denom
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - 2 * α) (by linarith : (0:ℝ) < 1 + α),
    mul_nonneg h0.le (sq_nonneg (α - 1 / 2))]

private theorem one_sub_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - α := by linarith

private theorem one_sub_two_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - 2 * α := by linarith

private theorem ratio_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  div_nonneg h0.le (one_sub_pos h1).le

private theorem ratio_lt_one {α : ℝ} (h1 : α < 1 / 2) : α / (1 - α) < 1 :=
  (div_lt_one (one_sub_pos h1)).mpr (by linarith)

private theorem p1_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 ≤ (α - 2 * α ^ 2) / denom α := by
  apply div_nonneg _ (denom_pos_aux h0 h1).le
  nlinarith

/-- Summability of the lead probabilities `n ↦ p_{n+1}`. -/
private theorem lead_summable {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    Summable (fun n : ℕ => stationary α (.lead n)) := by
  simp only [stationary]
  exact (summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_right _

/-- `∑ n, r^n p₁ = p₁ (1 - α) / (1 - 2α)`. -/
private theorem lead_tsum {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, stationary α (.lead n) = (α - 2 * α ^ 2) / denom α * (1 - α) / (1 - 2 * α) := by
  simp only [stationary]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)]
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  field_simp
  ring

private theorem poolExpGain_zero (α γ : ℝ) : poolExpGain α γ .zero = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_tie (α γ : ℝ) :
    poolExpGain α γ .tie = α * 2 + γ * (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead0 (α γ : ℝ) : poolExpGain α γ (.lead 0) = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_lead1 (α γ : ℝ) : poolExpGain α γ (.lead 1) = (1 - α) * 2 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead2 (α γ : ℝ) (n : ℕ) :
    poolExpGain α γ (.lead (n + 2)) = (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem othersExpGain_zero (α γ : ℝ) : othersExpGain α γ .zero = (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_tie (α γ : ℝ) :
    othersExpGain α γ .tie = (1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_lead (α γ : ℝ) (n : ℕ) : othersExpGain α γ (.lead n) = 0 := by
  rcases n with _ | _ | n <;> simp [othersExpGain, outcomeSum, othersGain]

/-- Balance at lead `k = n + 3 ≥ 3`: inflow from lead `k - 1` (pool block) and lead `k + 1`
(honest block). -/
theorem solution (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      α * BitcoinSelfishMining.stationary α (.lead (n + 1))
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead (n + 3)) := by
  have h1' := (one_sub_pos h1).ne'
  have key : α / (1 - α) = α + (1 - α) * (α / (1 - α)) ^ 2 := by
    field_simp
    ring
  simp only [stationary]
  have e2 : (α / (1 - α)) ^ (n + 2) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) := by ring
  have e3 : (α / (1 - α)) ^ (n + 3) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) ^ 2 := by ring
  rw [e2, e3]
  linear_combination ((α / (1 - α)) ^ (n + 1) * ((α - 2 * α ^ 2) / denom α)) * key
