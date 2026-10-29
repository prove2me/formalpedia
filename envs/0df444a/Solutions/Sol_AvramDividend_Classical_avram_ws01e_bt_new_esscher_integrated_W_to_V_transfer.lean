-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_esscher_integrated_W_to_V_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:54:32.948512+00:00
-- url     : https://prove2.me/submissions/c8c8797e-d2e2-4df0-9715-b2e326ff6c1b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Topology

/-- Exponential Esscher normalisation removes a constant logarithmic
derivative from an integrated positive-axis representation. -/
theorem solution
    (φ : ℝ) (W g : ℝ → ℝ)
    (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (hW : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + g t)) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      Real.exp (-(φ * b)) * W b =
        (Real.exp (-(φ * a)) * W a) * Real.exp (∫ t in a..b, g t) := by
  intro a b ha hab
  have hseg : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hgI : IntervalIntegrable g volume a b :=
    (hg.mono hseg).intervalIntegrable
  have hconstI : IntervalIntegrable (fun _ : ℝ => φ) volume a b :=
    continuous_const.intervalIntegrable a b
  have hInt : (∫ t in a..b, φ + g t) =
      φ * (b - a) + ∫ t in a..b, g t := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => φ) (g := g) hconstI hgI]
    rw [intervalIntegral.integral_const]
    ring
  calc
    Real.exp (-(φ * b)) * W b =
        Real.exp (-(φ * b)) *
          (W a * Real.exp (∫ t in a..b, φ + g t)) := by
            rw [hW a b ha hab]
    _ = (Real.exp (-(φ * a)) * W a) *
          Real.exp (∫ t in a..b, g t) := by
      rw [hInt, Real.exp_add]
      have he : Real.exp (-(φ * b)) *
          Real.exp (φ * (b - a)) = Real.exp (-(φ * a)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (-(φ * b)) * Real.exp (φ * (b - a))) *
              W a * Real.exp (∫ t in a..b, g t) := by ring
        _ = _ := by rw [he]
