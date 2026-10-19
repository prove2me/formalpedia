-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularFormCoordinateCoverLift_complexDriftCommutator_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/4ccd2f3d-1495-40f2-a128-6ed2f8c4b9a8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsMollifierEstimates_setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_tendsto_zero
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact

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
    {b : LogSpace n → ℂ} (hb : Continuous b)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator b
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  exact
    setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_tendsto_zero
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j)
      (fun {_} hS =>
        angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
          ha W j hS)
      hb hK
end Ehrhart.TorusHomogeneousFriedrichs
