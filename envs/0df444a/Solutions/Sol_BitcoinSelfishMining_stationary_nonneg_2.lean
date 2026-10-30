-- Prove2me | solution 2 for BitcoinSelfishMining.stationary_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:25:40.520404+00:00
-- url     : https://prove2.me/submissions/d0a8f4c2-42c1-4485-a410-6a6d2a02c635

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

/-- All stationary probabilities are nonnegative for `0 < α < 1/2`. -/
theorem solution (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) : 0 ≤ BitcoinSelfishMining.stationary α s := by
  have hD := denom_pos_aux h0 h1
  rcases s with _ | _ | n
  · simp only [stationary]
    exact div_nonneg (by linarith) hD.le
  · simp only [stationary]
    exact div_nonneg (mul_nonneg (one_sub_pos h1).le (by nlinarith [mul_pos h0 (one_sub_two_pos h1)]))
      hD.le
  · simp only [stationary]
    exact mul_nonneg (pow_nonneg (ratio_nonneg h0 h1) n) (p1_nonneg h0 h1)
