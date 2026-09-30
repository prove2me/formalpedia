-- Prove2me | solution 1 for FormalCapacity.Measure.temporal_density_capacityFlow_expanded
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T23:54:55.005315+00:00
-- url     : https://prove2.me/submissions/61f53fd8-0c31-4fba-bb82-87af97faabed

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Definitions.Def_capacityMeasureThreeLabel
import Definitions.Def_capacityTemporalFlow
import Theorems.Thm_FormalCapacity_Measure_ThreeLabelDensities_integral_canonicalScore_eq_components
import Theorems.Thm_FormalCapacity_Measure_ThreeLabelDensities_integrated_stability

set_option autoImplicit false

/-!
# The temporal capacity-flow inequality

This file proves the abstract form of equation (4.2).  The first theorem uses
finite block measures and an arbitrary measurable restriction map.  The second
specializes it to the density hypotheses discharged by the integrated
three-label stability theorem.  The final corollary expands the canonical
score into the triple and two weighted pair terms printed in (4.2).
-/

open MeasureTheory

namespace FormalCapacity.Measure

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]





/-- Density-level temporal capacity flow, derived—not assumed—from the
pointwise finite theorem and integration.  This form requires no measurable
partition-valued random variable: its sole temporal input is the integrated
coarsening score inequality `hcoarsen`. -/
theorem temporal_density_capacityFlow
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ)
    (hintEarly : early.IntegrableFor (q12 ∘ R) (q23 ∘ R) μEarly)
    (hintLate : late.IntegrableFor q12 q23 μLate)
    (hvalidEarly : ∀ᵐ x ∂μEarly, early.ValidAt x)
    (hvalidLate : ∀ᵐ y ∂μLate, late.ValidAt y)
    (hadmissibleEarly : ∀ᵐ x ∂μEarly,
      early.AdmissibleAt (q12 ∘ R) (q23 ∘ R) x)
    (hadmissibleLate : ∀ᵐ y ∂μLate, late.AdmissibleAt q12 q23 y)
    (hcoarsen :
      (∫ x, early.actualScore (q12 ∘ R) (q23 ∘ R) x ∂μEarly) ≤
        ∫ y, late.actualScore q12 q23 y ∂μLate) :
    densityCanonicalFlowGap early late μEarly μLate R q12 q23 ≤
      (∫ x, early.deficit12 x ∂μEarly) +
        (∫ x, early.deficit23 x ∂μEarly) +
        (∫ y, late.deficit13 y ∂μLate) := by
  have hearly := (early.integrated_stability (q12 ∘ R) (q23 ∘ R) μEarly
    hintEarly hvalidEarly hadmissibleEarly).1
  have hlate := (late.integrated_stability q12 q23 μLate
    hintLate hvalidLate hadmissibleLate).2
  unfold densityCanonicalFlowGap
  linarith





/-- Expansion of the score difference into triple mass plus the two weighted
pushforward differences. -/
theorem densityCanonicalFlowGap_eq_expanded
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ)
    (hintEarly : CanonicalComponentsIntegrable early (q12 ∘ R) (q23 ∘ R) μEarly)
    (hintLate : CanonicalComponentsIntegrable late q12 q23 μLate) :
    densityCanonicalFlowGap early late μEarly μLate R q12 q23 =
      densityCanonicalFlowGapExpanded early late μEarly μLate R q12 q23 := by
  have hearly := early.integral_canonicalScore_eq_components
    (q12 ∘ R) (q23 ∘ R) μEarly hintEarly.triple hintEarly.pair12 hintEarly.pair23
  have hlate := late.integral_canonicalScore_eq_components
    q12 q23 μLate hintLate.triple hintLate.pair12 hintLate.pair23
  unfold densityCanonicalFlowGap densityCanonicalFlowGapExpanded
  rw [hearly, hlate]
  simp only [Function.comp_apply]
  ring



end
end FormalCapacity.Measure




/-!
# The temporal capacity-flow inequality

This file proves the abstract form of equation (4.2).  The first theorem uses
finite block measures and an arbitrary measurable restriction map.  The second
specializes it to the density hypotheses discharged by the integrated
three-label stability theorem.  The final corollary expands the canonical
score into the triple and two weighted pair terms printed in (4.2).
-/

open MeasureTheory

open FormalCapacity.Measure



variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]














theorem solution
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ)
    (hintEarly : early.IntegrableFor (q12 ∘ R) (q23 ∘ R) μEarly)
    (hintLate : late.IntegrableFor q12 q23 μLate)
    (hcomponentsEarly : CanonicalComponentsIntegrable early (q12 ∘ R) (q23 ∘ R) μEarly)
    (hcomponentsLate : CanonicalComponentsIntegrable late q12 q23 μLate)
    (hvalidEarly : ∀ᵐ x ∂μEarly, early.ValidAt x)
    (hvalidLate : ∀ᵐ y ∂μLate, late.ValidAt y)
    (hadmissibleEarly : ∀ᵐ x ∂μEarly,
      early.AdmissibleAt (q12 ∘ R) (q23 ∘ R) x)
    (hadmissibleLate : ∀ᵐ y ∂μLate, late.AdmissibleAt q12 q23 y)
    (hcoarsen :
      (∫ x, early.actualScore (q12 ∘ R) (q23 ∘ R) x ∂μEarly) ≤
        ∫ y, late.actualScore q12 q23 y ∂μLate) :
    densityCanonicalFlowGapExpanded early late μEarly μLate R q12 q23 ≤
      (∫ x, early.deficit12 x ∂μEarly) +
        (∫ x, early.deficit23 x ∂μEarly) +
        (∫ y, late.deficit13 y ∂μLate) := by
  rw [← densityCanonicalFlowGap_eq_expanded early late μEarly μLate R q12 q23
    hcomponentsEarly hcomponentsLate]
  exact temporal_density_capacityFlow early late μEarly μLate R q12 q23
    hintEarly hintLate hvalidEarly hvalidLate hadmissibleEarly hadmissibleLate hcoarsen
