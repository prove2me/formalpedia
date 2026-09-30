-- Prove2me | solution 1 for FormalCapacity.Measure.ThreeLabelDensities.integrated_stability
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T23:53:24.315043+00:00
-- url     : https://prove2.me/submissions/ea473035-8459-41be-ac38-b2838ac361d8

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_capacityMeasureThreeLabel
import Theorems.Thm_FormalCapacity_Finite_threeLabel_stability

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





























/-- Pointwise density form of the sharp stability theorem. -/
theorem pointwise_stability (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) {x : α}
    (hv : d.ValidAt x) (hq : d.AdmissibleAt q12 q23 x) :
    d.canonicalScore q12 q23 x - d.deficit12 x - d.deficit23 x ≤
        d.actualScore q12 q23 x ∧
      d.actualScore q12 q23 x ≤ d.canonicalScore q12 q23 x + d.deficit13 x := by
  exact Finite.threeLabel_stability
    hv.beta123_nonneg hv.beta12_nonneg hv.beta23_nonneg hv.beta13_nonneg
    hv.marginal1 hv.marginal2 hv.marginal3 rfl rfl rfl
    hq.q12_nonneg hq.q12_le_one hq.q23_nonneg hq.q23_le_one hq.q_sum
    hq.middle_not_smallest

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








theorem solution (d : ThreeLabelDensities α) (q12 q23 : α → ℝ)
    (μ : Measure α) (hint : d.IntegrableFor q12 q23 μ)
    (hv : ∀ᵐ x ∂μ, d.ValidAt x)
    (hq : ∀ᵐ x ∂μ, d.AdmissibleAt q12 q23 x) :
    (∫ x, d.canonicalScore q12 q23 x ∂μ) - (∫ x, d.deficit12 x ∂μ) -
          (∫ x, d.deficit23 x ∂μ) ≤ ∫ x, d.actualScore q12 q23 x ∂μ ∧
      (∫ x, d.actualScore q12 q23 x ∂μ) ≤
        (∫ x, d.canonicalScore q12 q23 x ∂μ) +
          (∫ x, d.deficit13 x ∂μ) := by
  have hpointLower :
      (∀ᵐ x ∂μ, d.canonicalScore q12 q23 x - d.deficit12 x - d.deficit23 x ≤
        d.actualScore q12 q23 x) := by
    filter_upwards [hv, hq] with x hxv hxq
    exact (d.pointwise_stability q12 q23 hxv hxq).1
  have hpointUpper :
      (∀ᵐ x ∂μ, d.actualScore q12 q23 x ≤
        d.canonicalScore q12 q23 x + d.deficit13 x) := by
    filter_upwards [hv, hq] with x hxv hxq
    exact (d.pointwise_stability q12 q23 hxv hxq).2
  have hlower := integral_mono_ae
    ((hint.canonicalScore.sub hint.deficit12).sub hint.deficit23)
    hint.actualScore hpointLower
  have hupper := integral_mono_ae hint.actualScore
    (hint.canonicalScore.add hint.deficit13) hpointUpper
  have hlower' :
      (∫ x, d.canonicalScore q12 q23 x - d.deficit12 x - d.deficit23 x ∂μ) ≤
        ∫ x, d.actualScore q12 q23 x ∂μ := by
    simpa only [Pi.sub_apply] using hlower
  have hupper' :
      (∫ x, d.actualScore q12 q23 x ∂μ) ≤
        ∫ x, d.canonicalScore q12 q23 x + d.deficit13 x ∂μ := by
    simpa only [Pi.add_apply] using hupper
  have heq12 :
      (∫ x, d.canonicalScore q12 q23 x - d.deficit12 x ∂μ) =
        (∫ x, d.canonicalScore q12 q23 x ∂μ) - (∫ x, d.deficit12 x ∂μ) :=
    integral_sub hint.canonicalScore hint.deficit12
  have heqLower :
      (∫ x, d.canonicalScore q12 q23 x - d.deficit12 x - d.deficit23 x ∂μ) =
        (∫ x, d.canonicalScore q12 q23 x - d.deficit12 x ∂μ) -
          (∫ x, d.deficit23 x ∂μ) := by
    simpa only [Pi.sub_apply] using
      integral_sub (hint.canonicalScore.sub hint.deficit12) hint.deficit23
  have heqUpper :
      (∫ x, d.canonicalScore q12 q23 x + d.deficit13 x ∂μ) =
        (∫ x, d.canonicalScore q12 q23 x ∂μ) +
          (∫ x, d.deficit13 x ∂μ) :=
    integral_add hint.canonicalScore hint.deficit13
  rw [heqLower, heq12] at hlower'
  rw [heqUpper] at hupper'
  exact ⟨hlower', hupper'⟩
