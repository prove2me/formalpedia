-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyBergmanWeakProbabilityConvergence_of_radial_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/146caea6-10b4-44dd-9e3b-c9267fbfb617

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_tendsto_momentMovingRadialBergmanProbability_of_tests
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyBergmanWeakProbabilityConvergence_of_radial

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
    (htests : ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1)
                (momentNormalizedPotential (momentBodyOptimizer K)) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability
            (momentBodyOptimizer K))))) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) :=
  momentBodyBergmanWeakProbabilityConvergence_of_radial K p
    (tendsto_momentMovingRadialBergmanProbability_of_tests
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) htests)
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
