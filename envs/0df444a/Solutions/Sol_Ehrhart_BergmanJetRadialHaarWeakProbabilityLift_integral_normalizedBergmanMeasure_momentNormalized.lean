-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.integral_normalizedBergmanMeasure_momentNormalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/ce186b9d-3287-4eda-9da7-d560623d8d48

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSlope_continuous_normalizedDiagonalDensity

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
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ) :
    (∫ x : Space n, f x
      ∂(normalizedBergmanMeasure
        K k (momentNormalizedPotential F))) =
      ∫ x : Space n,
        f x * normalizedDiagonalDensity
          K k (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n)) := by
  have hmeas : Measurable
      (fun x : Space n =>
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x)) :=
    ENNReal.measurable_ofReal.comp
      (BergmanJetSlope.continuous_normalizedDiagonalDensity
        K hk (continuous_momentNormalizedPotential F)).measurable
  have hfinite :
      ∀ᵐ x : Space n ∂(volume : Measure (Space n)),
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [normalizedBergmanMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal
    (normalizedDiagonalDensity_momentNormalized_pos
      K hk F htransport x).le]
  simp [smul_eq_mul, mul_comm]
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
