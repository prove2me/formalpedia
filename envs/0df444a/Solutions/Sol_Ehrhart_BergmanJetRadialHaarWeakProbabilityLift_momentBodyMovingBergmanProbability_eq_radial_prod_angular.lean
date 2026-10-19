-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyMovingBergmanProbability_eq_radial_prod_angular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/d653ef5a-75a1-444d-a42f-4b9aa604a09a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentTorusBergmanProbability_eq_normalizedRadial_prod_angular

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
    {n : ℕ} (K : CenteredBody n) (k : ℕ) :
    momentBodyMovingBergmanProbability K k =
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) k).prod
            (momentNormalizedAngularHaarProbability n) := by
  apply Subtype.ext
  exact momentTorusBergmanProbability_eq_normalizedRadial_prod_angular
    K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
