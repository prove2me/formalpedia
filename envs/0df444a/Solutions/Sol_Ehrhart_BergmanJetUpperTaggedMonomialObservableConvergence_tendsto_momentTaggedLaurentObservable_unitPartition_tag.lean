-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.tendsto_momentTaggedLaurentObservable_unitPartition_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/f58c4fdb-e527-421f-8b91-a53cc56ead7e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetMovingMonomialObservableConvergence_tendsto_momentNormalized_moving_monomial_bounded_observable
import Theorems.Thm_Ehrhart_BergmanJetRoundedMonomialObservableConvergence_momentNormalizedPhase_dualGradient_maximizer
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_upperTaggedLatticeExponent_eq_unitPartition_tag
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_tendsto_upperTaggedLatticeExponent
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_unitPartition_tag_index_mem_scaledIntegerLattice

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        momentTaggedLaurentObservable F (k + 1) f
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) u)))
      atTop
      (𝓝 (f
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u))) := by
  have hraw :
      Tendsto
        (fun k : ℕ =>
          momentNormalizedLaurentObservable F k f
            (upperTaggedLatticeExponent k u))
        atTop
        (𝓝 (f
          (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u))) := by
    unfold momentNormalizedLaurentObservable
    exact tendsto_momentNormalized_moving_monomial_bounded_observable
      F htransport hu hdu
      (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      (momentNormalizedPhase_dualGradient_maximizer
        F htransport hu hdu)
      (fun k => upperTaggedLatticeExponent k u)
      (tendsto_upperTaggedLatticeExponent u)
      f hf C hC
  have hshift := hraw.comp (Filter.tendsto_add_atTop_nat 1)
  have htag (k : ℕ) :
      BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) u) ∈
        scaledIntegerLattice n (k + 1) :=
    unitPartition_tag_index_mem_scaledIntegerLattice k u
  simpa [Function.comp_def, momentTaggedLaurentObservable,
    upperTaggedLatticeExponent_eq_unitPartition_tag,
    htag] using hshift
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
