-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.tendsto_momentMovingRadialBergmanProbability_of_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8d78a58d-0e05-4888-8419-9edbaaae9354

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_integral_normalizedBergmanMeasure_momentNormalized

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
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (htests : ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F)))) :
    Tendsto
      (momentMovingRadialBergmanProbability K F htransport)
      atTop (𝓝 (momentRadialGibbsProbability F)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change
    Tendsto
      (fun k : ℕ =>
        ∫ x : Space n, f x
          ∂(normalizedBergmanMeasure
            K (k + 1) (momentNormalizedPotential F)))
      atTop
      (𝓝 (∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F)))
  have hEq :
      (fun k : ℕ =>
        ∫ x : Space n, f x
          ∂(normalizedBergmanMeasure
            K (k + 1) (momentNormalizedPotential F))) =
        fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)) := by
    funext k
    exact integral_normalizedBergmanMeasure_momentNormalized
      K (Nat.zero_lt_succ k) F htransport f
  rw [hEq]
  exact htests f
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
