-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyZeroGibbsProbability_eq_radial_prod_angular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/82fe2d8e-1aad-44a5-830a-d7b9362ffc03

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBergmanProbabilityTransfer_momentWeakTorusGibbsProbability_body_eq_zeroTime

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanNormalization LogPartitionConvexity MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman MomentWeakBergmanProbabilityEndpoint BergmanJetPartitionEndpoint
open BergmanJetTorusSlopeBridge BergmanJetBergmanProbabilityTransfer
open BergmanJetPortmanteauActualVolumeBridge
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
namespace Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyZeroGibbsProbability K p =
      (momentRadialGibbsProbability
        (momentBodyOptimizer K)).prod
          (momentNormalizedAngularHaarProbability n) := by
  apply Subtype.ext
  change
    sourceProbability (momentBodyTorusWeight K p) 0 =
      (finiteEnergySourceGibbsProbability
        (momentBodyOptimizer K)).prod (angularMeasure n)
  exact
    (momentWeakTorusGibbsProbability_body_eq_zeroTime K p).symm
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
