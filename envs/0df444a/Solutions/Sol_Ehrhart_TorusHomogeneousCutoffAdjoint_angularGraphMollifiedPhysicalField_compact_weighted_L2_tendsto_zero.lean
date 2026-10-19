-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousCutoffAdjoint.angularGraphMollifiedPhysicalField_compact_weighted_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/08e44b85-e7c6-445c-9492-010b307c5963

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularWeightedFormCoordinate_normalizedCoverMollification_compact_L2_tendsto_zero

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
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  let e : Fin n → ℕ → LogTorus n → ℂ :=
    fun j k q =>
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n =>
              (W r : EuclideanSpace ℂ (Fin n)) j)) k) q -
        (W q : EuclideanSpace ℂ (Fin n)) j
  have hvanish (j : Fin n) :
      Tendsto
        (fun k : ℕ => ∫ q in S, ‖e j k q‖ ^ 2 ∂μ)
        atTop (nhds 0) :=
    TorusHomogeneousFriedrichs.angularWeightedFormCoordinate_normalizedCoverMollification_compact_L2_tendsto_zero
        ha W j hS
  have hsum := tendsto_finsetSum Finset.univ
    (fun (j : Fin n) _ => hvanish j)
  have hint (j : Fin n) (k : ℕ) :
      IntegrableOn (fun q : LogTorus n => ‖e j k q‖ ^ 2) S μ := by
    have hmoll : Continuous
        (fun q : LogTorus n =>
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n =>
                  (W r : EuclideanSpace ℂ (Fin n)) j)) k) q) := by
      apply continuous_torusScalarRepresentative_of_periodic
      · exact (contDiff_normalizedCoverMollification
          (angularWeightedFormCoordinateCoverLift_locallyIntegrable
            ha W j) k 0).continuous
      · intro d
        exact normalizedCoverMollification_periodic
          (fun d' => complexTorusCoverLift_periodic
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) d') k d
    have hM : MemLp
        (fun q : LogTorus n =>
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n =>
                  (W r : EuclideanSpace ℂ (Fin n)) j)) k) q)
        2 (μ.restrict S) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (hmoll.aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact (hmoll.norm.pow 2).continuousOn.integrableOn_compact hS
    have hW : MemLp
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j)
        2 (μ.restrict S) := by
      exact ((MeasureTheory.Lp.memLp W).mono_measure
        Measure.restrict_le_self).continuousLinearMap_comp
          (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j)
    exact (hM.sub hW).norm.integrable_sq
  have hpoint (k : ℕ) (q : LogTorus n) :
      ‖torusFormRepresentative
          (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2 =
      ∑ j : Fin n, ‖e j k q‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
  have hident (k : ℕ) :
      (∫ q in S,
        ‖torusFormRepresentative
            (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2
          ∂μ) =
      ∑ j : Fin n, (∫ q in S, ‖e j k q‖ ^ 2 ∂μ) := by
    calc
      _ = ∫ q in S, ∑ j : Fin n, ‖e j k q‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with q
        exact hpoint k q
      _ = _ := MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => hint j k)
  have ht :
      Tendsto
        (fun k : ℕ =>
          ∑ j : Fin n, (∫ q in S, ‖e j k q‖ ^ 2 ∂μ))
        atTop (nhds 0) := by
    simpa using hsum
  exact ht.congr'
    (Filter.Eventually.of_forall (fun k => (hident k).symm))
end Ehrhart.TorusHomogeneousCutoffAdjoint
