-- Prove2me | solution 2 for BitcoinSelfishMining.stationary_balance
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:27:27.110927+00:00
-- url     : https://prove2.me/submissions/5ab2074c-1a9a-42da-bd31-da9c8851c4fa

import Definitions.Def_BitcoinSelfishMining
import Theorems.Thm_BitcoinSelfishMining_balance_lead
import Theorems.Thm_BitcoinSelfishMining_balance_one
import Theorems.Thm_BitcoinSelfishMining_balance_tie
import Theorems.Thm_BitcoinSelfishMining_balance_two
import Theorems.Thm_BitcoinSelfishMining_balance_zero

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

/-- The paper's distribution is stationary for the chain: at every state `s`,
`p_s = Σ_t p_t · P(t → s)`, the sum running over all states (`stateSum`). -/
theorem solution (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by
  unfold stateSum
  rcases s with _ | _ | _ | _ | _ | k
  · -- state 0: inflow from 0, 0' and lead 2
    rw [tsum_eq_single 1 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_zero α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
  · -- the tie: inflow from lead 1
    rw [tsum_eq_single 0 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_tie α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
  · -- lead 1: inflow from 0
    rw [tsum_eq_single 0 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_one α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
  · -- lead 2: inflow from lead 1 and lead 3
    rw [tsum_eq_sum (s := {0, 2}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_two α h0 h1
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · exact absurd rfl hb.1
      · simp [P, outcomeSum, step]
      · have : b ≠ 0 := by omega
        simp [P, outcomeSum, step, this]
  · -- lead 3: inflow from lead 2 and lead 4
    rw [tsum_eq_sum (s := {1, 3}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      have := balance_lead α h0 h1 0
      simp only [Nat.zero_add] at this
      linear_combination this
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb.1
      · have h1' : b ≠ 1 := by omega
        simp [P, outcomeSum, step, h1']
  · -- lead k + 4 ≥ 4: inflow from lead k + 3 and lead k + 5
    rw [tsum_eq_sum (s := {k + 2, k + 4}) ?_, Finset.sum_pair (by omega)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      have := balance_lead α h0 h1 (k + 1)
      simp only [add_assoc, Nat.reduceAdd] at this
      linear_combination this
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
      · have h1' : b ≠ k := by omega
        have h0' : b ≠ k + 2 := by omega
        simp [P, outcomeSum, step, h1', h0']
