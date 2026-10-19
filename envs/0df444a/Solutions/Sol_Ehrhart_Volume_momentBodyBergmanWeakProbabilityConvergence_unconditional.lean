-- Prove2me | solution 1 for Ehrhart.Volume.momentBodyBergmanWeakProbabilityConvergence_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/38561b7a-f96b-4ae4-8abc-18f99eb799f0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyBergmanWeakProbabilityConvergence_of_radial_tests
import Theorems.Thm_Ehrhart_Volume_momentNormalizedDiagonalRadialWeakTests_unconditional

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Volume
open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
namespace Ehrhart.Volume
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) :=
  momentBodyBergmanWeakProbabilityConvergence_of_radial_tests K p
    (momentNormalizedDiagonalRadialWeakTests_unconditional
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K))
end Ehrhart.Volume
