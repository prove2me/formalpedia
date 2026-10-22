-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_esscher_laplace_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:21:35.250755+00:00
-- url     : https://prove2.me/submissions/b67d3fe5-6543-4e2b-8086-6ec533bd3ace

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_tonelli
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_measure_atom_transform
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Exact ENNReal Laplace transform of the Esscher-shifted Lévy double tail. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume) =
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal
          (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) := by
  calc
    ENNReal.ofReal (θ ^ 2) *
        (∫⁻ t : ℝ, ∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ ∂volume) =
      ENNReal.ofReal (θ ^ 2) *
        (∫⁻ z : ℝ, ∫⁻ t : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂volume ∂μ) :=
      congrArg (fun u : ENNReal => ENNReal.ofReal (θ ^ 2) * u)
        (gaussian_double_tail_tonelli μ φ θ)
    _ = _ := gaussian_double_tail_measure_atom_transform μ φ θ hφ hθ
