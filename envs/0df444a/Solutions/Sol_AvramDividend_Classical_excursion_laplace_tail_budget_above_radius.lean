-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_tail_budget_above_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:30:00.209223+00:00
-- url     : https://prove2.me/submissions/13764f28-998c-416a-916a-b9b313cc3604

import Mathlib

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ : Measure ℝ) (s R : ℝ) (hs : 0 < s)
    (hsupport : μ (Iio (0 : ℝ)) = 0)
    (δ : ENNReal)
    (hdecay : ENNReal.ofReal (Real.exp (-(s * R))) + δ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) +
      δ * μ (Ioi R) ≤ μ Set.univ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x))) := by fun_prop
  have hind : δ * μ (Ioi R) = ∫⁻ x, (Ioi R).indicator (fun _ => δ) x ∂μ := by
    rw [lintegral_indicator_const measurableSet_Ioi]
  rw [hind, ← lintegral_add_left hmeas, ← lintegral_one]
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]; convert hsupport using 2; ext; simp
  refine lintegral_mono_ae (hae.mono fun x hx => ?_)
  by_cases hxR : x ∈ Ioi R
  · rw [indicator_of_mem hxR]
    refine le_trans (add_le_add_left (ENNReal.ofReal_le_ofReal ?_) _) hdecay
    exact Real.exp_le_exp.2 (by have : R < x := hxR; nlinarith)
  · rw [indicator_of_notMem hxR, add_zero, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by nlinarith))
