-- Prove2me | solution 1 for BitcoinSelfishErgodic.distN_zero_lead_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:56:34.908449+00:00
-- url     : https://prove2.me/submissions/71fc9b06-98dc-44bc-a5bc-cc8dfab87a52

import Definitions.Def_BitcoinSelfishErgodic
import Theorems.Thm_BitcoinSelfishMining_stationary_balance
import Theorems.Thm_BitcoinSelfishMining_total_mass
import Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
import Theorems.Thm_BitcoinSelfishMining_threshold
import Theorems.Thm_BitcoinSelfishUnique_stationary_unique
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_one
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_succ
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_zero
import Theorems.Thm_BitcoinSelfishErgodic_isDist_delta
import Theorems.Thm_BitcoinSelfishErgodic_isDist_distN
import Theorems.Thm_BitcoinSelfishErgodic_le_one_of_isDist

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

/-- Uniform form of the inflow at the leads `n + 1 ≥ 1`. -/
private theorem dist_lead_add_one (α γ : ℝ) (μ : State → ℝ) (n : ℕ) :
    dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
  rcases n with _ | n
  · exact dist_lead_one α γ μ
  · exact dist_lead_succ α γ μ n

private theorem dist_summable {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => dist α γ μ (.lead n)) := by
  rw [← summable_nat_add_iff 1]
  have : (fun n : ℕ => dist α γ μ (.lead (n + 1))) =
      fun n => α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
    funext n; exact dist_lead_add_one α γ μ n
  rw [this]
  exact (hμ.mul_left α).add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α))

private theorem dist_lead_tsum {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    ∑' n : ℕ, dist α γ μ (.lead n) =
      α * μ .zero + α * ∑' n : ℕ, μ (.lead n)
        + (1 - α) * (∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1)) := by
  rw [(dist_summable (α := α) (γ := γ) hμ).tsum_eq_zero_add, dist_lead_zero]
  have e : ∀ n : ℕ, dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) :=
    dist_lead_add_one α γ μ
  simp_rw [e]
  rw [(hμ.mul_left α).tsum_add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α)),
    tsum_mul_left, tsum_mul_left]
  have h2 := hμ.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
  rw [show ∑' n : ℕ, μ (.lead (n + 2)) = ∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1) by
    linarith]
  ring

private theorem delta_lead_summable (t : State) :
    Summable (fun n : ℕ => delta t (.lead n)) := by
  rcases t with _ | _ | j
  · simp [delta]
  · simp [delta]
  · have : (fun n : ℕ => delta (.lead j) (.lead n)) = fun n => if n = j then (1:ℝ) else 0 := by
      funext n; simp [delta]
    rw [this]
    exact (hasSum_ite_eq j (1:ℝ)).summable

private theorem dist_lead_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m) (m : ℕ) :
    dist α γ μ (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  rcases m with _ | m
  · rw [dist_lead_zero, pow_zero, mul_one]
    have := le_one_of_isDist μ hμ .zero
    have := hμ.nonneg .zero
    nlinarith
  · rw [dist_lead_add_one, ← ratio_step h1 m]
    have ha := hb m
    have hb2 := hb (m + 2)
    have h1' : 0 ≤ 1 - α := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ha h0.le, mul_le_mul_of_nonneg_left hb2 h1']

private theorem distN_lead_le_aux {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m)
    (n m : ℕ) : distN α γ μ n (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  induction n generalizing m with
  | zero => exact hb m
  | succ n ih => exact dist_lead_le h0 h1 (isDist_distN α γ h0 h1 μ hμ n) hC ih m

/-- Geometric domination of the lead probabilities of the chain started at `zero`, uniformly
in time: `P(X_n = lead m) ≤ (α / (1 - α))^m` for every `n`. -/
theorem solution (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (n m : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n (.lead m) ≤
      (α / (1 - α)) ^ m := by
  have := distN_lead_le_aux (γ := γ) h0 h1 (isDist_delta .zero) (C := 1) le_rfl
    (fun m => by simpa [delta] using pow_nonneg (ratio_nonneg h0 h1) m) n m
  simpa using this
