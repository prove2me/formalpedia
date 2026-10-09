-- Prove2me | solution 1 for AvramDividend.Classical.esscher_jump_compensator_difference_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:18:24.476462+00:00
-- url     : https://prove2.me/submissions/59a9fca8-a79b-4e4b-9a15-0a6ee7542377

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0) (φ s : ℝ)
    (hJφ : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ)))) μ)
    (hJplus : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-((φ + s) * (z : ℝ)))) μ) :
    (∫ z : ℝ≥0,
      Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ)))) ∂μ) =
      (∫ z : ℝ≥0, 1 - Real.exp (-((φ + s) * (z : ℝ))) ∂μ) -
        (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂μ) := by
  have hf :
      (fun z : ℝ≥0 =>
        Real.exp (-(φ * (z : ℝ))) *
          (1 - Real.exp (-(s * (z : ℝ))))) =
      (fun z : ℝ≥0 =>
        (1 - Real.exp (-((φ + s) * (z : ℝ)))) -
          (1 - Real.exp (-(φ * (z : ℝ))))) := by
    funext z
    have he :
        Real.exp (-((φ + s) * (z : ℝ))) =
          Real.exp (-(φ * (z : ℝ))) *
            Real.exp (-(s * (z : ℝ))) := by
      rw [show -((φ + s) * (z : ℝ)) =
        -(φ * (z : ℝ)) + -(s * (z : ℝ)) by ring]
      exact Real.exp_add _ _
    rw [he]
    ring
  rw [hf, integral_sub hJplus hJφ]
