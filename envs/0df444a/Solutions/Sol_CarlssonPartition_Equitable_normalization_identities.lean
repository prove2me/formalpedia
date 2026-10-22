-- Prove2me | solution 1 for CarlssonPartition.Equitable.normalization_identities
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:38:39.253858+00:00
-- url     : https://prove2.me/submissions/d142e4ff-b4aa-4183-b28a-d8c57bf627ba

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

set_option autoImplicit false
open Filter Topology MeasureTheory CarlssonPartition.Equitable

theorem solution (I : Instance) (hI : I.Standing)
    (S : Set Plane) (hS : NullMeasurableSet S volume) (hSR : S ⊆ I.R) :
    (∫ x in S, Real.sqrt (I.fSub S x)) = (∫ x in S, Real.sqrt (I.f x)) / Real.sqrt (I.pr S) ∧
    (∫ x in S, ‖x - I.x0‖ * I.fSub S x) = (∫ x in S, ‖x - I.x0‖ * I.f x) / I.pr S := by
  have hpr : 0 ≤ I.pr S := by
    unfold Instance.pr
    refine integral_nonneg_of_ae ?_
    rw [Filter.EventuallyLE, ae_restrict_iff'₀ hS]
    exact Filter.Eventually.of_forall fun x hx => hI.2.2.2.1 x (hSR hx)
  constructor
  · rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Instance.fSub]
    rw [Real.sqrt_div' _ hpr]
  · rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Instance.fSub]
    ring
