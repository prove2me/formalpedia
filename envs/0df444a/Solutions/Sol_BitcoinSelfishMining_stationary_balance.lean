-- Prove2me | solution 1 for BitcoinSelfishMining.stationary_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:49:57.146915+00:00
-- url     : https://prove2.me/submissions/1f91b761-6b3d-4c8c-a9f3-0acb932ef9e8

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
    have : (α / (1 - α)) = α + (1 - α) * (α / (1 - α)) ^ 2 := by field_simp; try ring
    calc (α / (1 - α)) ^ (n + 2) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) := by ring
      _ = (α / (1 - α)) ^ (n + 1) * (α + (1 - α) * (α / (1 - α)) ^ 2) := by rw [← this]
      _ = _ := by ring
  rw [key]; ring


noncomputable def cc (α : ℝ) : ℝ := (α - 2 * α ^ 2) / denom α

theorem st_lead (α : ℝ) (n : ℕ) : stationary α (.lead n) = (α / (1 - α)) ^ n * cc α := rfl

theorem r_lt (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) : α / (1 - α) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

theorem r_nn (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  div_nonneg h0.le (by linarith)

theorem summ_lead (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (k : ℕ) (x : ℝ) :
    Summable (fun n : ℕ => stationary α (.lead (n + k)) * x) := by
  simp only [st_lead, pow_add]
  have := (summable_geometric_of_lt_one (r_nn α h0 h1) (r_lt α h0 h1)).mul_right
    ((α / (1 - α)) ^ k * cc α * x)
  exact this.congr (fun n => by ring)

-- fe7906ea
theorem V2 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      BitcoinSelfishMining.stationary α (.lead 0) * (α / (1 - α)) ^ 2 * (1 - α) / (1 - 2 * α) := by
  simp only [st_lead, pow_add]
  have e : (fun n : ℕ => (α / (1 - α)) ^ n * (α / (1 - α)) ^ 2 * cc α)
      = fun n => (α / (1 - α)) ^ n * ((α / (1 - α)) ^ 2 * cc α) := funext fun n => by ring
  rw [e, tsum_mul_right, tsum_geometric_of_lt_one (r_nn α h0 h1) (r_lt α h0 h1)]
  have h2 : (1 - α) ≠ 0 := by linarith
  have h3 : (1 - 2 * α) ≠ 0 := by linarith
  have h4 : 1 - α / (1 - α) = (1 - 2 * α) / (1 - α) := by field_simp; try ring
  rw [h4]; field_simp; try ring

theorem tail_eval (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, stationary α (.lead (n + 2)) = cc α * (α ^ 2 / ((1 - α) * (1 - 2 * α))) := by
  rw [V2 α h0 h1, st_lead]
  have h2 : (1 - α) ≠ 0 := by linarith
  have h3 : (1 - 2 * α) ≠ 0 := by linarith
  field_simp; try ring

theorem tsum_split (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (f : ℕ → ℝ) (x : ℝ)
    (hf : ∀ n, f (n + 2) = stationary α (.lead (n + 2)) * x) :
    ∑' n, f n = f 0 + f 1 + (∑' n : ℕ, stationary α (.lead (n + 2))) * x := by
  have hs2 : Summable (fun n => f (n + 2)) := by
    simp only [hf]; exact summ_lead α h0 h1 2 x
  have hs : Summable f := (summable_nat_add_iff 2).1 hs2
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hs).tsum_eq_zero_add]
  simp only [hf]
  rw [tsum_mul_right]
  ring

-- 599c9a2d
theorem V3 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishMining.stationary α) = 1 := by
  unfold stateSum
  rw [tsum_split α h0 h1 (fun n => stationary α (.lead n)) 1 (fun n => by simp)]
  simp only [mul_one]
  rw [tail_eval α h0 h1]
  have hd := (dpos α h0 h1).ne'
  have h2 : (1 - α) ≠ 0 := by linarith
  have h3 : (1 - 2 * α) ≠ 0 := by linarith
  simp only [stationary, cc, denom] at *
  field_simp
  have hn : α ^ 2 * (2 * α - 4) + 1 ≠ 0 := by intro h; apply hd; linear_combination h
  rw [div_eq_iff hn]
  ring

theorem pe_lead (α γ : ℝ) (n : ℕ) : poolExpGain α γ (.lead (n + 2)) = (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

-- 17380c2d
theorem V4 (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.poolRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * (α * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α (.lead 1) * ((1 - α) * 2)
        + (∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2))) * ((1 - α) * 1) := by
  unfold poolRevenue stateSum
  rw [tsum_split α h0 h1 _ ((1 - α) * 1) (fun n => by simp only [pe_lead])]
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]
  ring

-- e9f154e0
theorem V5 (α γ : ℝ) :
    BitcoinSelfishMining.othersRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * ((1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α .zero * ((1 - α) * 1) := by
  unfold othersRevenue stateSum
  have e : ∀ n, stationary α (.lead n) * othersExpGain α γ (.lead n) = 0 := fun n => by
    simp [othersExpGain, outcomeSum, othersGain]
  simp only [e, tsum_zero]
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]
  ring

-- 3c5af946
theorem V6 (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α γ = BitcoinSelfishMining.closedForm α γ := by
  unfold relativeRevenue closedForm
  rw [V4 α γ h0 h1, V5 α γ, tail_eval α h0 h1]
  have hd := (dpos α h0 h1)
  have h2 : (0 : ℝ) < 1 - α := by linarith
  have h3 : (0 : ℝ) < 1 - 2 * α := by linarith
  have hden : (0:ℝ) < 1 - α * (1 + (2 - α) * α) := by nlinarith [pow_pos h0 3]
  simp only [stationary, cc]
  set D := denom α with hD
  have hDn := hd.ne'
  have h2' := h2.ne'
  have h3' := h3.ne'
  have h3'' : 1 - α * 2 ≠ 0 := by linarith
  have hden'' : 1 - α * (1 + α * (2 - α)) ≠ 0 := by nlinarith
  have hsum : (1 - α) * (α - 2 * α ^ 2) / D * (α * 2 + γ * (1 - α) * 1) +
        (α / (1 - α)) ^ 1 * ((α - 2 * α ^ 2) / D) * ((1 - α) * 2) +
      (α - 2 * α ^ 2) / D * (α ^ 2 / ((1 - α) * (1 - 2 * α))) * ((1 - α) * 1) +
      ((1 - α) * (α - 2 * α ^ 2) / D * ((1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1) +
        (1 - 2 * α) / D * ((1 - α) * 1)) = (1 - α * (1 + (2 - α) * α)) / D := by
    field_simp
    ring
  rw [hsum, div_eq_div_iff (by positivity) hden.ne']
  field_simp
  ring

theorem diff (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    relativeRevenue α γ - α =
      α * (1 - α) ^ 2 * (α * (3 - 2 * γ) - (1 - γ)) / (1 - α * (1 + (2 - α) * α)) := by
  rw [V6 α γ h0 h1]
  unfold closedForm
  have hden : (0:ℝ) < 1 - α * (1 + (2 - α) * α) := by nlinarith [pow_pos h0 3]
  have hden' := hden.ne'
  rw [eq_div_iff hden', sub_mul, div_mul_cancel₀ _ hden']
  ring

theorem gt_iff (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    relativeRevenue α γ > α ↔ α * (3 - 2 * γ) - (1 - γ) > 0 := by
  have hden : (0:ℝ) < 1 - α * (1 + (2 - α) * α) := by nlinarith [pow_pos h0 3]
  have hp : 0 < α * (1 - α) ^ 2 := by have : (0:ℝ) < 1 - α := by linarith
                                      positivity
  have hd := diff α γ h0 h1
  constructor
  · intro h
    have : 0 < α * (1 - α) ^ 2 * (α * (3 - 2 * γ) - (1 - γ)) / (1 - α * (1 + (2 - α) * α)) := by
      rw [← hd]; linarith
    rw [div_pos_iff_of_pos_right hden] at this
    exact pos_of_mul_pos_right this hp.le
  · intro h
    have : 0 < α * (1 - α) ^ 2 * (α * (3 - 2 * γ) - (1 - γ)) / (1 - α * (1 + (2 - α) * α)) :=
      div_pos (mul_pos hp h) hden
    rw [← hd] at this; linarith

-- 806647ff
theorem V7 (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    BitcoinSelfishMining.relativeRevenue α γ > α ↔ α > BitcoinSelfishMining.profitThreshold γ := by
  rw [gt_iff α γ h0 h1]
  unfold profitThreshold
  have h3 : (0:ℝ) < 3 - 2 * γ := by linarith
  rw [gt_iff_lt, gt_iff_lt, div_lt_iff₀ h3]
  constructor <;> intro h <;> linarith

-- e326859d
theorem V8 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 0 > α ↔ α > 1 / 3 := by
  rw [gt_iff α 0 h0 h1]
  constructor <;> intro h <;> linarith

-- 720b0d19
theorem V9 (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 1 > α := by
  rw [gt_iff α 1 h0 h1]; linarith


-- 422bef84
theorem V1 (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by
  unfold stateSum
  rcases s with _ | _ | m
  · rw [tsum_eq_single 1 (fun n hn => by
      rcases n with _ | _ | n <;> simp_all [P, outcomeSum, step])]
    simp [P, outcomeSum, step, outcomeProb]
    linear_combination T4 α h0 h1
  · rw [tsum_eq_single 0 (fun n hn => by
      rcases n with _ | _ | n <;> simp_all [P, outcomeSum, step])]
    simp [P, outcomeSum, step, outcomeProb]
    linear_combination T5 α h0 h1
  · rcases m with _ | k
    · rw [tsum_eq_single 0 (fun n hn => by
        rcases n with _ | _ | n <;> simp_all [P, outcomeSum, step])]
      simp [P, outcomeSum, step, outcomeProb]
      linear_combination T6 α h0 h1
    · have hne : k ≠ k + 2 := by omega
      rw [tsum_eq_sum (s := {k, k + 2}) (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rcases n with _ | _ | n <;> simp_all [P, outcomeSum, step] <;> omega)]
      rw [Finset.sum_pair hne]
      have e1 : P α γ (.lead k) (.lead (k + 1)) = α := by
        rcases k with _ | _ | k <;> simp [P, outcomeSum, step, outcomeProb]
      have e2 : P α γ (.lead (k + 2)) (.lead (k + 1)) = 1 - α := by
        simp [P, outcomeSum, step, outcomeProb]; ring
      have e3 : P α γ .zero (.lead (k + 1)) = 0 := by simp [P, outcomeSum, step]
      have e4 : P α γ .tie (.lead (k + 1)) = 0 := by simp [P, outcomeSum, step]
      beta_reduce
      rw [e1, e2, e3, e4]
      rcases k with _ | k
      · linear_combination T7 α h0 h1
      · linear_combination T8 α h0 h1 k

end S229BSM

theorem solution (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by
  apply S229BSM.V1 <;> assumption

