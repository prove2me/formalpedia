-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/298a7ad6-4961-4d52-89f5-e9bc13614242

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedLp_aestronglyMeasurable_base
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularScalarCoverLift_normalizedCoverMollification_localL2_tendsto_zero

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
    (f : angularWeightedScalarL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n => f r)) k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  apply angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
    ha (angularWeightedLp_aestronglyMeasurable_base f)
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
  · intro K hK
    exact angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
      ha f hK
  · intro k
    exact (contDiff_normalizedCoverMollification
      (angularWeightedScalarCoverLift_locallyIntegrable ha f) k 0).continuous
  · intro k d
    exact normalizedCoverMollification_periodic
      (fun e => complexTorusCoverLift_periodic
        (fun q : LogTorus n => f q) e) k d
  · intro K hK
    exact
      angularScalarCoverLift_normalizedCoverMollification_localL2_tendsto_zero
        ha f hK
  · exact hS
end Ehrhart.TorusHomogeneousFriedrichs
