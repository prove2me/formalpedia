-- Prove2me | solution 1 for Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentTorusBergmanProbability_eq_normalizedRadial_prod_angular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/72d7fb34-83b4-4335-b07a-88b4d445e8e7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSlope_continuous_normalizedDiagonalDensity
import Theorems.Thm_Ehrhart_BergmanJetBergmanProbabilityTransfer_momentTorusBergmanProbability_eq_base_withDensity

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
    (F : SourceFiniteEnergyPotential K) :
    momentTorusBergmanProbability K F k =
      (normalizedBergmanMeasure
        K k (momentNormalizedPotential F)).prod
          (angularMeasure n) := by
  have hmeas : Measurable
      (fun x : Space n =>
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x)) :=
    ENNReal.measurable_ofReal.comp
      (BergmanJetSlope.continuous_normalizedDiagonalDensity
        K hk (continuous_momentNormalizedPotential F)).measurable
  rw [momentTorusBergmanProbability_eq_base_withDensity K hk F]
  change
    ((volume : Measure (Space n)).prod (angularMeasure n)).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal
            (normalizedDiagonalDensity
              K k (momentNormalizedPotential F) q.1)) =
      ((volume : Measure (Space n)).withDensity
        (fun x : Space n =>
          ENNReal.ofReal
            (normalizedDiagonalDensity
              K k (momentNormalizedPotential F) x))).prod
          (angularMeasure n)
  exact (MeasureTheory.prod_withDensity_left hmeas).symm
end Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
