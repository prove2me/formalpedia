-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_eps_plus_inverse_grid_rate_implies_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:30:45.10254+00:00
-- url     : https://prove2.me/submissions/827f1517-e0a7-418d-bd3d-334540d7fd5c

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
open Filter
open scoped Topology
noncomputable section

/-- A nonnegative grid error bounded by any positive epsilon plus a vanishing inverse-grid term tends to zero. -/
theorem solution
    (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hEps : ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
        a m ≤ ε + K / ((m + 1 : ℕ) : ℝ)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun m => lt_of_lt_of_le hb (ha m))
  · intro b hb
    have hb2 : 0 < b / 2 := by linarith
    obtain ⟨K, hK, hRate⟩ := hEps (b / 2) hb2
    have hKlim : Tendsto
        (fun m : ℕ => K / ((m + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, mul_zero, one_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
    filter_upwards [hKlim.eventually_lt_const hb2] with m hm
    have hr := hRate m
    linarith
