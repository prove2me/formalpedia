-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularWeightedFormCoordinate_normalizedCoverMollification_compact_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/27efa4c4-f7ce-43c6-bf83-1aa988e2a996

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedLp_aestronglyMeasurable_base
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularFormCoordinateCoverLift_normalizedCoverMollification_localL2_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousFriedrichs
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusDolbeault
open TorusWeightedBaseAE TorusWeakDolbeaultMollification TorusStrongCoverMollificationDensity
open TorusStrongWeightedTorusDescent TorusFriedrichsMollifierEstimates
open TorusWeightedAdjointMollification BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousFriedrichs
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a) (j : Fin n)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n =>
                    (W r : EuclideanSpace ℂ (Fin n)) j)) k) q -
            (W q : EuclideanSpace ℂ (Fin n)) j‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hbase : AEStronglyMeasurable
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) j)
      (sourceTorusBaseMeasure n) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp_aestronglyMeasurable
      (angularWeightedLp_aestronglyMeasurable_base W)
  apply angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
    ha hbase
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W j)
  · intro K hK
    exact angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
      ha W j hK
  · intro k
    exact (contDiff_normalizedCoverMollification
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j) k 0).continuous
  · intro k d
    exact normalizedCoverMollification_periodic
      (fun e => complexTorusCoverLift_periodic
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j) e) k d
  · intro K hK
    exact
      angularFormCoordinateCoverLift_normalizedCoverMollification_localL2_tendsto_zero
        ha W j hK
  · exact hS
end Ehrhart.TorusHomogeneousFriedrichs
