-- Prove2me | solution 1 for BitcoinSelfishErgodic.dist_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:51:05.016584+00:00
-- url     : https://prove2.me/submissions/60dda0fa-695c-4a58-8674-039341692068

import Definitions.Def_BitcoinSelfishErgodic
import Theorems.Thm_BitcoinSelfishMining_stationary_balance
import Theorems.Thm_BitcoinSelfishMining_total_mass
import Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
import Theorems.Thm_BitcoinSelfishMining_threshold
import Theorems.Thm_BitcoinSelfishUnique_stationary_unique
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_one
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_succ
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_zero
import Theorems.Thm_BitcoinSelfishErgodic_dist_tie
import Theorems.Thm_BitcoinSelfishErgodic_dist_zero

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

/-- One step of the chain preserves nonnegativity (for `0 ≤ α ≤ 1`). -/
theorem solution (α γ : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : ∀ s, 0 ≤ μ s) (s : BitcoinSelfishMining.State) :
    0 ≤ BitcoinSelfishErgodic.dist α γ μ s := by
  have h1' : 0 ≤ 1 - α := by linarith
  rcases s with _ | _ | _ | _ | n
  · rw [dist_zero]; have := hμ .zero; have := hμ .tie; have := hμ (.lead 1); positivity
  · rw [dist_tie]; have := hμ (.lead 0); positivity
  · rw [dist_lead_zero]; have := hμ .zero; positivity
  · rw [dist_lead_one]; have := hμ (.lead 0); have := hμ (.lead 2); positivity
  · rw [dist_lead_succ]; have := hμ (.lead (n + 1)); have := hμ (.lead (n + 3)); positivity
