-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularScalarCoverLift_normalizedCoverMollification_localL2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/37c21f20-2dce-4a30-90d4-34778413ee6a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_localL2_tendsto_zero

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
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverMollification
              (complexTorusCoverLift
                (fun q : LogTorus n => f q)) k x -
            complexTorusCoverLift
              (fun q : LogTorus n => f q) x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  exact normalizedCoverMollification_localL2_tendsto_zero
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
    hK
    (angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
      ha f hK.cthickening)
end Ehrhart.TorusHomogeneousFriedrichs
