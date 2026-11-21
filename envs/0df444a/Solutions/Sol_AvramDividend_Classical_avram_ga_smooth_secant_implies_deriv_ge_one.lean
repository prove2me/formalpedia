-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_smooth_secant_implies_deriv_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:41:40.279623+00:00
-- url     : https://prove2.me/submissions/47c91d26-0ac5-45ae-a367-09d8f4daf45c

import Mathlib.Analysis.Calculus.Deriv.Slope
open Set
noncomputable section

theorem solution
    (V : ℝ → ℝ)
    (hSec : ∀ x y : ℝ, x ≤ y → y - x ≤ V y - V x)
    (y : ℝ) (hDiff : DifferentiableAt ℝ V y) :
    1 ≤ deriv V y := by
  have hMono : Monotone (V - id) := by
    intro x z hxz
    change V x - x ≤ V z - z
    linarith [hSec x z hxz]
  have hd : 0 ≤ deriv (V - id) y := hMono.deriv_nonneg
  have heq : deriv (V - id) y = deriv V y - 1 := by
    simpa only [deriv_id] using (deriv_sub hDiff differentiableAt_id)
  linarith
