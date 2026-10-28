-- Prove2me | solution 1 for AvramDividend.Classical.surviving_record_prefix_budget_le_killed_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:34:43.626869+00:00
-- url     : https://prove2.me/submissions/4d2c6e72-3d97-49b0-99f1-815436d4517f

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators Classical

/-! Bound a survived finite prefix by the full killed record reward series. -/
theorem solution (τ : ℝ≥0∞) (q h : ℝ) (hh : 0 ≤ h)
    (c : ℕ → ℝ≥0∞) (u : ℕ → ℝ≥0) (N : ℕ)
    (hc : ∀ k : ℕ, k ≤ N → c k = (u k : ℝ≥0∞))
    (hmono : ∀ k : ℕ, k ≤ N → c k ≤ c N)
    (hSurvive : (u N : ℝ≥0∞) < τ) :
    (∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
        ENNReal.ofReal h) ≤
    (∑' k : ℕ,
      if c k < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * (c k).toReal)))
      else 0) := by
  classical
  have hclock (k : ℕ) (hk : k ≤ N) : c k < τ := by
    calc
      c k ≤ c N := hmono k hk
      _ = (u N : ℝ≥0∞) := hc N le_rfl
      _ < τ := hSurvive
  have hterm (k : ℕ) (hk : k ≤ N) :
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
        ENNReal.ofReal h =
      (if c k < τ then
        ENNReal.ofReal (h * Real.exp (-(q * (c k).toReal)))
       else 0) := by
    rw [if_pos (hclock k hk), hc k hk]
    simp only [ENNReal.coe_toReal, ENNReal.ofReal_mul hh, mul_comm]
  calc
    (∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
        ENNReal.ofReal h) =
    (∑ k ∈ Finset.range (N + 1),
      if c k < τ then
        ENNReal.ofReal (h * Real.exp (-(q * (c k).toReal)))
      else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ ≤ (∑' k : ℕ,
      if c k < τ then
        ENNReal.ofReal (h * Real.exp (-(q * (c k).toReal)))
      else 0) := ENNReal.sum_le_tsum (Finset.range (N + 1))
