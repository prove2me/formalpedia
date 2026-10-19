-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyBergmanWeakProbabilityConvergence_of_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/54fb297d-6fbd-4243-b5c5-6c10f12b1f53

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyMovingBergmanProbability_eq_radial_prod_angular
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyZeroGibbsProbability_eq_radial_prod_angular

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
    (p : LogSpace n)
    (hrad : Tendsto
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K))
      atTop
      (𝓝 (momentRadialGibbsProbability
        (momentBodyOptimizer K)))) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) := by
  have hpair :
      Tendsto
        (fun k : ℕ =>
          (momentMovingRadialBergmanProbability
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) k,
           momentNormalizedAngularHaarProbability n))
        atTop
        (𝓝 (momentRadialGibbsProbability
              (momentBodyOptimizer K),
            momentNormalizedAngularHaarProbability n)) :=
    hrad.prodMk_nhds tendsto_const_nhds
  have hproduct :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  change
    Tendsto (momentBodyMovingBergmanProbability K)
      atTop (𝓝 (momentBodyZeroGibbsProbability K p))
  have hsequence :
      momentBodyMovingBergmanProbability K =
        fun k : ℕ =>
          (momentMovingRadialBergmanProbability
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) k).prod
                (momentNormalizedAngularHaarProbability n) := by
    funext k
    exact momentBodyMovingBergmanProbability_eq_radial_prod_angular
      K k
  rw [hsequence,
    momentBodyZeroGibbsProbability_eq_radial_prod_angular]
  exact hproduct
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
