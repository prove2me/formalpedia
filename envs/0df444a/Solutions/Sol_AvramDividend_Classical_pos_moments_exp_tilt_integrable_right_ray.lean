-- Prove2me | solution 1 for AvramDividend.Classical.pos_moments_exp_tilt_integrable_right_ray
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:09:01.577034+00:00
-- url     : https://prove2.me/submissions/c792f1ca-a6f3-49fb-94a1-796d297d72f6

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    (μ : Measure ℝ)
    (h : ∀ u : ℝ, 0 < u → Integrable (fun x : ℝ => Real.exp (u * x)) μ)
    (t : ℝ) (ht : -1 < t) :
    Integrable (fun x : ℝ => Real.exp (t * x))
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))) := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x)) :=
    (Real.measurable_exp).ennreal_ofReal
  have htop : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp x) < ⊤ :=
    ae_of_all μ (fun x => lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  rw [integrable_withDensity_iff hf htop]
  have hmain := h (t + 1) (by linarith)
  convert hmain using 1
  funext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [← Real.exp_add]
  congr 1
  ring