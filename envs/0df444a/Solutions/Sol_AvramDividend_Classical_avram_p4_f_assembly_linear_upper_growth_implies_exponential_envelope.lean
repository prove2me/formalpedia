-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:21:15.113104+00:00
-- url     : https://prove2.me/submissions/ae5c85d7-7f2e-4461-bc76-f9fb9e2fc6f8

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

/-- An at-most-linear candidate admits an Esscher exponential envelope. -/
theorem solution
    (w : ℝ → ℝ) (B L K θ : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hB : B ≤ K) (hL : L ≤ K * θ)
    (hneg : ∀ y : ℝ, y < 0 → w y ≤ 0)
    (hlinear : ∀ y : ℝ, 0 ≤ y → w y ≤ B + L * y) :
    ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  intro y
  by_cases hy : 0 ≤ y
  · have hExp : 1 + θ * y ≤ Real.exp (θ * y) := by
      simpa [add_comm] using (Real.add_one_le_exp (θ * y))
    have hMul : K * (1 + θ * y) ≤ K * Real.exp (θ * y) :=
      mul_le_mul_of_nonneg_left hExp hK
    have hSlope : L * y ≤ (K * θ) * y :=
      mul_le_mul_of_nonneg_right hL hy
    calc
      w y ≤ B + L * y := hlinear y hy
      _ ≤ K * (1 + θ * y) := by nlinarith [hB, hSlope]
      _ ≤ K * Real.exp (θ * y) := hMul
  · have hylt : y < 0 := lt_of_not_ge hy
    exact (hneg y hylt).trans (mul_nonneg hK (le_of_lt (Real.exp_pos _)))

