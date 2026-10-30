-- Prove2me | solution 1 for BitcoinSelfishMining.denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:29:06.685501+00:00
-- url     : https://prove2.me/submissions/20460314-e0ea-430b-b2ee-b66d93136e80

import Definitions.Def_BitcoinSelfishMining
namespace S229BSM
open BitcoinSelfishMining

noncomputable def g (u : State) (c : ℝ) : ℝ :=
  match u with
  | .lead _ => c
  | _ => 0

theorem hs (u : State) (c : ℝ) : HasSum (fun n : ℕ => if u = State.lead n then c else 0) (g u c) := by
  cases u with
  | zero => simp [g]
  | tie => simp [g]
  | lead m =>
    have := hasSum_ite_eq m c
    simp only [g, State.lead.injEq]
    convert this using 2 with n
    simp [eq_comm]

theorem col (u : State) (c : ℝ) :
    (if u = State.zero then c else 0) + (if u = State.tie then c else 0) + g u c = c := by
  cases u <;> simp [g]

theorem T3 (α γ : ℝ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stateSum (fun t => BitcoinSelfishMining.P α γ s t) = 1 := by
  have h := ((hs (step s .pool) (outcomeProb α γ .pool)).add
    (hs (step s .honestOnPool) (outcomeProb α γ .honestOnPool))).add
    (hs (step s .honestOnOthers) (outcomeProb α γ .honestOnOthers))
  simp only [stateSum, P, outcomeSum]
  rw [h.tsum_eq]
  have := col (step s .pool) (outcomeProb α γ .pool)
  have := col (step s .honestOnPool) (outcomeProb α γ .honestOnPool)
  have := col (step s .honestOnOthers) (outcomeProb α γ .honestOnOthers)
  have hsum : outcomeProb α γ .pool + outcomeProb α γ .honestOnPool + outcomeProb α γ .honestOnOthers = 1 := by
    simp [outcomeProb]; ring
  linarith

theorem T1 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 < 2 * α ^ 3 - 4 * α ^ 2 + 1 := by nlinarith [pow_pos h0 3]

theorem dpos (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < denom α := T1 α h0 h1

theorem T2 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) : 0 ≤ BitcoinSelfishMining.stationary α s := by
  have hd := dpos α h0 h1
  have hq : 0 ≤ α - 2 * α ^ 2 := by nlinarith
  cases s with
  | zero => exact div_nonneg (by linarith) hd.le
  | tie => exact div_nonneg (mul_nonneg (by linarith) hq) hd.le
  | lead n => exact mul_nonneg (pow_nonneg (div_nonneg h0.le (by linarith)) _) (div_nonneg hq hd.le)

theorem T4 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .zero =
      (1 - α) * BitcoinSelfishMining.stationary α .zero
        + BitcoinSelfishMining.stationary α .tie
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 1) := by
  have hd := (dpos α h0 h1).ne'
  have h2 : (1 - α) ≠ 0 := by linarith
  simp only [stationary]
  field_simp
  ring

theorem T5 (α : ℝ) (_h0 : 0 < α) (_h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .tie =
      (1 - α) * BitcoinSelfishMining.stationary α (.lead 0) := by
  simp only [stationary]; ring

theorem T6 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 0) =
      α * BitcoinSelfishMining.stationary α .zero := by
  simp only [stationary]; ring

theorem T7 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 1) =
      α * BitcoinSelfishMining.stationary α (.lead 0)
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 2) := by
  have hd := (dpos α h0 h1).ne'
  have h2 : (1 - α) ≠ 0 := by linarith
  simp only [stationary]
  field_simp
  ring

theorem T8 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      α * BitcoinSelfishMining.stationary α (.lead (n + 1))
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead (n + 3)) := by
  have h2 : (1 - α) ≠ 0 := by linarith
  simp only [stationary]
  have key : (α / (1 - α)) ^ (n + 2) = α * (α / (1 - α)) ^ (n + 1) + (1 - α) * (α / (1 - α)) ^ (n + 3) := by
    have : (α / (1 - α)) = α + (1 - α) * (α / (1 - α)) ^ 2 := by field_simp; ring
    calc (α / (1 - α)) ^ (n + 2) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) := by ring
      _ = (α / (1 - α)) ^ (n + 1) * (α + (1 - α) * (α / (1 - α)) ^ 2) := by rw [← this]
      _ = _ := by ring
  rw [key]; ring

end S229BSM

theorem solution (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 < 2 * α ^ 3 - 4 * α ^ 2 + 1 := by
  apply S229BSM.T1 <;> assumption

