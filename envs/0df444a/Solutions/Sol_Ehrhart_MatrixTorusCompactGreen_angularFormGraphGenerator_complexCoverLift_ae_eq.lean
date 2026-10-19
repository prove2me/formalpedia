-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularFormGraphGenerator_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/db64b209-6890-4ff0-9697-b6c240a6ecfe

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_complexTorusCoverLift_barPartialRepresentative_eq
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedTorus_complexCoverLift_ae_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff
namespace Ehrhart.MatrixTorusCompactGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (F : LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) (j : Fin n) :
    complexTorusCoverLift
      (fun q : LogTorus n =>
        (angularBarPartialL2OfRepresentative a F hD q :
          EuclideanSpace ℂ (Fin n)) j)
        =ᵐ[(volume : Measure (LogSpace n))]
      (fun z => barPartialCoordinate F z j) := by
  have hrow := hD.coeFn_toLp
  have hj :
      (fun q : LogTorus n =>
        (angularBarPartialL2OfRepresentative a F hD q :
          EuclideanSpace ℂ (Fin n)) j)
        =ᵐ[angularWeightedTorusMeasure a]
      (fun q : LogTorus n =>
        (torusFunctionBarPartialRepresentative F q :
          EuclideanSpace ℂ (Fin n)) j) := by
    filter_upwards [hrow] with q hq
    exact congrFun (congrArg WithLp.ofLp hq) j
  have h := angularWeightedTorus_complexCoverLift_ae_eq ha hj
  rw [complexTorusCoverLift_barPartialRepresentative_eq
    F hperiod j] at h
  exact h
end Ehrhart.MatrixTorusCompactGreen
