-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/308eb400-0444-4c88-909b-8c7946c08bc1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusFriedrichsMollifierEstimates TorusWeightedAdjointMollification
open TorusStrongWeightedTorusDescent TorusStrongWeightedRadialCutoff TorusFriedrichsCutoff
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousCutoffAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a) (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => f r)) k) q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  apply angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
    (F := fun k q =>
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => f r)) k) q)
    (f := fun q => f q)
    (m := m)
  · intro k S hS
    let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
    let : IsLocallyFiniteMeasure μ :=
      angularWeightedTorusMeasure_isLocallyFinite ha
    have hc : Continuous
        (torusScalarRepresentative
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun r : LogTorus n => f r)) k)) := by
      apply continuous_torusScalarRepresentative_of_periodic
      · exact (contDiff_normalizedCoverMollification
          (angularWeightedScalarCoverLift_locallyIntegrable
            ha f) k 0).continuous
      · intro d
        exact normalizedCoverMollification_periodic
          (fun d' => complexTorusCoverLift_periodic
            (fun q : LogTorus n => f q) d') k d
    have hM : MemLp
        (torusScalarRepresentative
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun r : LogTorus n => f r)) k))
        2 (μ.restrict S) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (hc.aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact (hc.norm.pow 2).continuousOn.integrableOn_compact hS
    exact (hM.sub ((MeasureTheory.Lp.memLp f).mono_measure
      Measure.restrict_le_self)).norm.integrable_sq
  · intro S hS
    exact TorusHomogeneousFriedrichs.angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
        ha f hS
end Ehrhart.TorusHomogeneousCutoffAdjoint
