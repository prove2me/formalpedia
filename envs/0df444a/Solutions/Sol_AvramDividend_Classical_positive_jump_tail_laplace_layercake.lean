-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_laplace_layercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T21:09:01.985148+00:00
-- url     : https://prove2.me/submissions/7cef28d6-70b0-4970-a342-41d7778acc74

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z : ℝ≥0,
       ENNReal.ofReal (∫ t in (0 : ℝ)..(z : ℝ), Real.exp (-θ * t)) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ),
        μ {z : ℝ≥0 | t < (z : ℝ)} *
          ENNReal.ofReal (Real.exp (-θ * t)) := by
  have hf : 0 ≤ᵐ[μ] (fun z : ℝ≥0 => (z : ℝ)) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hm : AEMeasurable (fun z : ℝ≥0 => (z : ℝ)) μ :=
    (by fun_prop : Measurable (fun z : ℝ≥0 => (z : ℝ))).aemeasurable
  have hi : ∀ t > 0,
      IntervalIntegrable (fun u : ℝ => Real.exp (-θ * u)) volume 0 t := by
    intro t ht
    have hc : Continuous (fun u : ℝ => Real.exp (-θ * u)) := by fun_prop
    exact hc.intervalIntegrable 0 t
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ Real.exp (-θ * t) :=
    Filter.Eventually.of_forall (fun t => by positivity)
  simpa using
    (MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul μ
      (f := fun z : ℝ≥0 => (z : ℝ))
      (g := fun t : ℝ => Real.exp (-θ * t)) hf hm hi hn)
