-- Prove2me | solution 1 for Ehrhart.Volume.ehrhart_volume_inequality_for_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/66cacc53-a824-4e78-b3c7-0bc0b95ebcf3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_normalizedVolume_le_sharpConstant_of_momentBodyWeakProbability
import Theorems.Thm_Ehrhart_Volume_momentBodyBergmanWeakProbabilityConvergence_unconditional

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
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (S : Set (Space n)) (hconvex : Convex ℝ S)
    (hcompact : IsCompact S) (hinterior : (interior S).Nonempty)
    (hcentered : barycenter S = 0)
    (hlattice : interiorLatticePoints S = {0}) :
    normalizedVolume S ≤ ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) := by
  let K : CenteredBody n :=
    { carrier := S
      convex := hconvex
      compact := hcompact
      fullDimensional := hinterior
      centered := hcentered
      uniqueInteriorLatticePoint := hlattice }
  simpa [K, sharpConstant] using
    normalizedVolume_le_sharpConstant_of_momentBodyWeakProbability hn K
      (momentBodyBergmanWeakProbabilityConvergence_unconditional
        K (0 : LogSpace n))
end Ehrhart.Volume
