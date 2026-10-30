-- Prove2me | solution 1 for BitcoinSelfishUnique.stationary_unique
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:13:55.492113+00:00
-- url     : https://prove2.me/submissions/579341d2-e9a3-41f8-a945-c5568a9f263e

import Definitions.Def_BitcoinSelfishUnique
import Theorems.Thm_BitcoinSelfishUnique_balance_lead_of
import Theorems.Thm_BitcoinSelfishUnique_balance_one_of
import Theorems.Thm_BitcoinSelfishUnique_balance_tie_of
import Theorems.Thm_BitcoinSelfishUnique_balance_two_of
import Theorems.Thm_BitcoinSelfishUnique_geometric_of_isStationary

open BitcoinSelfishUnique BitcoinSelfishMining

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

private theorem stat_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (s : State) :
    0 ≤ stationary α s := by
  have hD := denom_pos_aux h0 h1
  rcases s with _ | _ | n
  · simp only [stationary]
    exact div_nonneg (by linarith) hD.le
  · simp only [stationary]
    exact div_nonneg (mul_nonneg (one_sub_pos h1).le (by nlinarith [mul_pos h0 (one_sub_two_pos h1)]))
      hD.le
  · simp only [stationary]
    exact mul_nonneg (pow_nonneg (ratio_nonneg h0 h1) n) (p1_nonneg h0 h1)

private theorem stat_lead_summable {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    Summable (fun n : ℕ => stationary α (.lead n)) := by
  simp only [stationary]
  exact (summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_right _

private theorem stat_lead_tsum {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, stationary α (.lead n) = (α - 2 * α ^ 2) / denom α * (1 - α) / (1 - 2 * α) := by
  simp only [stationary]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)]
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  field_simp
  ring

private theorem stat_total_mass {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    stateSum (stationary α) = 1 := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  have h2'' : 1 - α * 2 ≠ 0 := by rwa [mul_comm]
  unfold stateSum
  rw [stat_lead_tsum h0 h1]
  simp only [stationary]
  field_simp
  unfold denom
  ring

private theorem stat_balance_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    stationary α .zero =
      (1 - α) * stationary α .zero + stationary α .tie + (1 - α) * stationary α (.lead 1) := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  simp only [stationary]
  field_simp
  ring

private theorem stat_balance_tie (α : ℝ) :
    stationary α .tie = (1 - α) * stationary α (.lead 0) := by
  simp only [stationary]
  ring

private theorem stat_balance_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    stationary α (.lead 0) = α * stationary α .zero := by
  have hD := (denom_pos_aux h0 h1).ne'
  simp only [stationary]
  field_simp

private theorem stat_balance_two {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    stationary α (.lead 1) = α * stationary α (.lead 0) + (1 - α) * stationary α (.lead 2) := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  simp only [stationary]
  field_simp
  ring

private theorem stat_balance_lead {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    stationary α (.lead (n + 2)) =
      α * stationary α (.lead (n + 1)) + (1 - α) * stationary α (.lead (n + 3)) := by
  have h1' := (one_sub_pos h1).ne'
  have key : α / (1 - α) = α + (1 - α) * (α / (1 - α)) ^ 2 := by
    field_simp
    ring
  simp only [stationary]
  have e2 : (α / (1 - α)) ^ (n + 2) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) := by ring
  have e3 : (α / (1 - α)) ^ (n + 3) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) ^ 2 := by ring
  rw [e2, e3]
  linear_combination ((α / (1 - α)) ^ (n + 1) * ((α - 2 * α ^ 2) / denom α)) * key

private theorem inflow_zero (α γ : ℝ) (π : State → ℝ) :
    stateSum (fun t => π t * P α γ t .zero) =
      (1 - α) * π .zero + π .tie + (1 - α) * π (.lead 1) := by
  unfold stateSum
  rw [tsum_eq_single 1 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · simp [P, outcomeSum, step]
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]

private theorem inflow_tie (α γ : ℝ) (π : State → ℝ) :
    stateSum (fun t => π t * P α γ t .tie) = (1 - α) * π (.lead 0) := by
  unfold stateSum
  rw [tsum_eq_single 0 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]
    · simp [P, outcomeSum, step]

private theorem inflow_one (α γ : ℝ) (π : State → ℝ) :
    stateSum (fun t => π t * P α γ t (.lead 0)) = α * π .zero := by
  unfold stateSum
  rw [tsum_eq_single 0 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]
    · simp [P, outcomeSum, step]

private theorem inflow_two (α γ : ℝ) (π : State → ℝ) :
    stateSum (fun t => π t * P α γ t (.lead 1)) = α * π (.lead 0) + (1 - α) * π (.lead 2) := by
  unfold stateSum
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

private theorem inflow_lead (α γ : ℝ) (π : State → ℝ) (n : ℕ) :
    stateSum (fun t => π t * P α γ t (.lead (n + 2))) =
      α * π (.lead (n + 1)) + (1 - α) * π (.lead (n + 3)) := by
  unfold stateSum
  rcases n with _ | k
  · rw [tsum_eq_sum (s := {1, 3}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      ring
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb.1
      · have h1' : b ≠ 1 := by omega
        simp [P, outcomeSum, step, h1']
  · rw [tsum_eq_sum (s := {k + 2, k + 4}) ?_, Finset.sum_pair (by omega)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      ring
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
      · have h1' : b ≠ k := by omega
        have h0' : b ≠ k + 2 := by omega
        simp [P, outcomeSum, step, h1', h0']

/-- The second-order recurrence at every lead `k + 1 ≥ 2` (uniform form of `balance_two_of`
and `balance_lead_of`). -/
private theorem recur {α γ : ℝ} {π : State → ℝ} (h : IsStationary α γ π) (k : ℕ) :
    π (.lead (k + 1)) = α * π (.lead k) + (1 - α) * π (.lead (k + 2)) := by
  rcases k with _ | k
  · exact balance_two_of α γ π h
  · exact balance_lead_of α γ π h k

private theorem q_step {α γ : ℝ} {π : State → ℝ} (h1 : α < 1 / 2) (h : IsStationary α γ π)
    (n : ℕ) :
    π (.lead (n + 2)) - α / (1 - α) * π (.lead (n + 1)) =
      π (.lead (n + 1)) - α / (1 - α) * π (.lead n) := by
  have h1' := (one_sub_pos h1).ne'
  have e := recur h n
  have hr : (1 - α) * (α / (1 - α)) = α := mul_div_cancel₀ _ h1'
  apply mul_left_cancel₀ h1'
  linear_combination (-1 : ℝ) * e + (π (.lead n) - π (.lead (n + 1))) * hr

private theorem q_const {α γ : ℝ} {π : State → ℝ} (h1 : α < 1 / 2) (h : IsStationary α γ π)
    (n : ℕ) :
    π (.lead (n + 1)) - α / (1 - α) * π (.lead n) =
      π (.lead 1) - α / (1 - α) * π (.lead 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [q_step h1 h n, ih]

/-- Closed form: `p n - L = r ^ n (p 0 - L)` where `L = c / (1 - r)`. -/
private theorem closed_form {α γ : ℝ} {π : State → ℝ} (h1 : α < 1 / 2) (h : IsStationary α γ π)
    (n : ℕ) :
    π (.lead n) - (π (.lead 1) - α / (1 - α) * π (.lead 0)) / (1 - α / (1 - α)) =
      (α / (1 - α)) ^ n *
        (π (.lead 0) - (π (.lead 1) - α / (1 - α) * π (.lead 0)) / (1 - α / (1 - α))) := by
  have hr : 1 - α / (1 - α) ≠ 0 := (sub_pos.mpr (ratio_lt_one h1)).ne'
  induction n with
  | zero => simp
  | succ n ih =>
    have e := q_const h1 h n
    set r := α / (1 - α) with hr_def
    set c := π (.lead 1) - r * π (.lead 0) with hc
    have e' : π (.lead (n + 1)) = c + r * π (.lead n) := by linear_combination e
    rw [e', pow_succ]
    have : c - c / (1 - r) = - (r * (c / (1 - r))) := by
      field_simp
      ring
    linear_combination r * ih + this

/-- For `0 < α < 1/2` the stationary distribution of the selfish-mining chain is unique: every
`IsStationary α γ π` coincides with the paper's `stationary α` at every state. -/
theorem solution (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h0 : 0 < α) (h1 : α < 1 / 2) (h : BitcoinSelfishUnique.IsStationary α γ π)
    (s : BitcoinSelfishMining.State) : π s = BitcoinSelfishMining.stationary α s := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  have hr0 := ratio_nonneg h0 h1
  have hr1 := ratio_lt_one h1
  -- all leads in terms of `π 1`
  have hgeom : ∀ n, π (.lead n) = (α / (1 - α)) ^ n * π (.lead 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [geometric_of_isStationary α γ π h0 h1 h n, ih, pow_succ]; ring
  have hone := balance_one_of α γ π h
  have htie := balance_tie_of α γ π h
  -- total mass pins `π 0`
  have hmass := h.mass
  unfold stateSum at hmass
  have hsum : ∑' n : ℕ, π (.lead n) = ∑' n : ℕ, (α / (1 - α)) ^ n * π (.lead 0) :=
    tsum_congr hgeom
  rw [hsum, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1] at hmass
  have hinv : (1 - α / (1 - α))⁻¹ = (1 - α) / (1 - 2 * α) := by
    have e : 1 - α / (1 - α) = (1 - 2 * α) / (1 - α) := by
      field_simp
      ring
    rw [e, inv_div]
  rw [hinv, htie, hone] at hmass
  have key : π .zero * ((1 - 2 * α) + (1 - α) * α * (1 - 2 * α) + (1 - α) * α) = 1 - 2 * α := by
    have e : (1 - α) / (1 - 2 * α) * (α * π .zero) * (1 - 2 * α) = (1 - α) * (α * π .zero) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ h2']
    linear_combination (1 - 2 * α) * hmass - e
  have hz : π .zero = (1 - 2 * α) / denom α := by
    rw [eq_div_iff hD]
    unfold denom
    linear_combination key
  rcases s with _ | _ | n
  · simp only [stationary]; exact hz
  · rw [htie, hone, hz]; simp only [stationary]; field_simp
  · rw [hgeom n, hone, hz]; simp only [stationary]; field_simp
