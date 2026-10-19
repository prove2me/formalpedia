-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularWeightedTorus_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/dc36aacf-086c-488c-ba3f-2b41a3396458

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_complexTorusCoverLift_ae_eq
import Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedTorus_ae_eq_base

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
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f g : LogTorus n → ℂ}
    (h : f =ᵐ[angularWeightedTorusMeasure a] g) :
    complexTorusCoverLift f =ᵐ[(volume : Measure (LogSpace n))]
      complexTorusCoverLift g := by
  apply complexTorusCoverLift_ae_eq
  simpa [sourceTorusBaseMeasure, unweightedTorusMeasure] using
    angularWeightedTorus_ae_eq_base ha h
end Ehrhart.MatrixTorusCompactGreen
