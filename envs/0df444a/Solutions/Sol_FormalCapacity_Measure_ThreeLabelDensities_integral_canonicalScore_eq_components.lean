-- Prove2me | solution 1 for FormalCapacity.Measure.ThreeLabelDensities.integral_canonicalScore_eq_components
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T23:52:04.827104+00:00
-- url     : https://prove2.me/submissions/5e480fe1-181c-4467-ba47-e054b114a64c

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_capacityMeasureThreeLabel

set_option autoImplicit false

/-!
# Measure-theoretic three-label stability

This file lifts the scalar theorem `FormalCapacity.Finite.threeLabel_stability`
to densities over an arbitrary measure space.  Pair deficits are defined
pointwise, proved nonnegative almost everywhere from the block-capacity
constraints, and then integrated.  Nothing here assumes a stochastic process
or a Brownian law.
-/

open MeasureTheory

namespace FormalCapacity.Measure



namespace ThreeLabelDensities

variable {α : Type*}































variable [MeasurableSpace α]











end ThreeLabelDensities
end FormalCapacity.Measure




/-!
# Measure-theoretic three-label stability

This file lifts the scalar theorem `FormalCapacity.Finite.threeLabel_stability`
to densities over an arbitrary measure space.  Pair deficits are defined
pointwise, proved nonnegative almost everywhere from the block-capacity
constraints, and then integrated.  Nothing here assumes a stochastic process
or a Brownian law.
-/

open MeasureTheory

open FormalCapacity.Measure



open FormalCapacity.Measure.ThreeLabelDensities

variable {α : Type*}































variable [MeasurableSpace α]










theorem solution
    (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) (μ : Measure α)
    (h123 : Integrable d.canonical123 μ)
    (h12 : Integrable (fun x ↦ q12 x * d.canonical12 x) μ)
    (h23 : Integrable (fun x ↦ q23 x * d.canonical23 x) μ) :
    (∫ x, d.canonicalScore q12 q23 x ∂μ) =
      (∫ x, d.canonical123 x ∂μ) +
        (∫ x, q12 x * d.canonical12 x ∂μ) +
        (∫ x, q23 x * d.canonical23 x ∂μ) := by
  change (∫ x, (d.canonical123 x + q12 x * d.canonical12 x) +
      q23 x * d.canonical23 x ∂μ) = _
  have hfirst :
      (∫ x, d.canonical123 x + q12 x * d.canonical12 x ∂μ) =
        (∫ x, d.canonical123 x ∂μ) +
          (∫ x, q12 x * d.canonical12 x ∂μ) :=
    integral_add h123 h12
  have hall :
      (∫ x, (d.canonical123 x + q12 x * d.canonical12 x) +
          q23 x * d.canonical23 x ∂μ) =
        (∫ x, d.canonical123 x + q12 x * d.canonical12 x ∂μ) +
          (∫ x, q23 x * d.canonical23 x ∂μ) := by
    simpa only [Pi.add_apply] using integral_add (h123.add h12) h23
  rw [hall, hfirst]
