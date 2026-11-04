-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_all_power_tail_bounds_force_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:58:25.471974+00:00
-- url     : https://prove2.me/submissions/378c6573-3710-4bcd-9a07-05c92b08a15c

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

theorem solution
    (R a C : ℝ) (hR : 1 < R) (ha : 0 ≤ a)
    (hbound : ∀ k : ℕ, R ^ k * a ≤ C) : a = 0 := by
  have hRpos : 0 < R := by linarith
  have hlim : Tendsto (fun k : ℕ => C / R ^ k) atTop (nhds 0) := by
    have hpow : Tendsto (fun k : ℕ => R ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hR
    simpa using (tendsto_const_nhds.div_atTop hpow)
  have hle : ∀ k : ℕ, a ≤ C / R ^ k := by
    intro k
    exact (le_div_iff₀ (pow_pos hRpos k)).2 (by
      simpa [mul_comm] using hbound k)
  have hzero : a ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  exact le_antisymm hzero ha
