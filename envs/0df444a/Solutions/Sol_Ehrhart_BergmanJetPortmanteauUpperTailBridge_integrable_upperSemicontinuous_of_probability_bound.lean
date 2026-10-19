-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauUpperTailBridge.integrable_upperSemicontinuous_of_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/285d098c-5f67-41fe-aea7-c67fc2d3557f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauUpperTailBridge
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauUpperTailBridge
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (μ : ProbabilityMeasure X) {g : X → ℝ} {C : ℝ}
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C) (hnonneg : ∀ x : X, 0 ≤ g x)
    (hbound : ∀ x : X, g x ≤ C) :
    Integrable g (μ : Measure X) := by
  refine (integrable_const C).mono' hg.measurable.aestronglyMeasurable ?_
  have hCabs : |C| = C := abs_of_nonneg hC
  exact Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg x),
      hCabs] using hbound x
end Ehrhart.BergmanJetPortmanteauUpperTailBridge
