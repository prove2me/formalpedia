-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/35d2d25e-b884-4494-81df-8bf9bc39ea92

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularMollifiedPhysicalAdjointDriftCommutator_tendsto_zero

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
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun ℓ : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hzloc : LocallyIntegrable
      (complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)))
      (volume : Measure (LogSpace n)) := by
    have hzero :
        complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)) =
          (fun _ : LogSpace n => (0 : ℂ)) := by
      funext x
      rfl
    rw [hzero]
    exact locallyIntegrable_zero
  have hzmem : ∀ {K : Set (LogSpace n)}, IsCompact K →
      MemLp (complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)))
        2 ((volume : Measure (LogSpace n)).restrict K) := by
    intro K _
    change MemLp (fun _ : LogSpace n => (0 : ℂ)) 2
      ((volume : Measure (LogSpace n)).restrict K)
    exact MeasureTheory.MemLp.zero
  have h :=
    angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
      (f := fun _ : LogTorus n => (0 : ℂ))
      ha aestronglyMeasurable_zero hzloc hzmem
      (F := fun ℓ => angularMollifiedPhysicalAdjointDriftCommutator W ℓ)
      (fun ℓ => continuous_angularMollifiedPhysicalAdjointDriftCommutator
        ha ha2 W ℓ)
      (fun ℓ d =>
        TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic W ℓ d)
      (by
        intro K hK
        simpa [complexTorusCoverLift] using
          (TorusHomogeneousFriedrichs.angularMollifiedPhysicalAdjointDriftCommutator_tendsto_zero
              ha ha2 W hK))
      hS
  simpa using h
end Ehrhart.TorusHomogeneousCutoffAdjoint
