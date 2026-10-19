-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.upperSemicontinuous_momentTorusClampedTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/28fbc05c-46f8-4403-9013-d8b824569b50

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_upperSemicontinuous_momentTorusTailPositiveSecant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusClampedTailPositiveSecant
        K F htransport p r t ht) := by
  have h : UpperSemicontinuous
      (fun q : LogTorus n =>
        max (0 : ℝ)
          (momentTorusTailPositiveSecant
            K F htransport p r t ht q)) :=
    upperSemicontinuous_const.sup
      (upperSemicontinuous_momentTorusTailPositiveSecant
        K F htransport p r t ht)
  have hclamp :
      (fun q : LogTorus n =>
        max (0 : ℝ)
          (momentTorusTailPositiveSecant
            K F htransport p r t ht q)) =
        momentTorusClampedTailPositiveSecant
          K F htransport p r t ht := by
    funext q
    rfl
  rw [hclamp] at h
  exact h
end Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
