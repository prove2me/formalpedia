-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/7ede4c29-636d-40c9-b33d-0e82e3fbc0df

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
import Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedLp_tendsto_of_squared_error_integral
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero

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
    (W : angularWeightedFormL2 a) (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        (angularClosedMollifiedDrift_fixedRadialCutoff_memLp
          ha ha2 W ℓ m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q))
      atTop (nhds (0 : angularWeightedScalarL2 a)) := by
  have hlocal : ∀ (ℓ : ℕ) {S : Set (LogTorus n)}, IsCompact S →
      IntegrableOn
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
            (0 : ℂ)‖ ^ 2)
        S (angularWeightedTorusMeasure a) := by
    intro ℓ S hS
    let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
      angularWeightedTorusMeasure_isLocallyFinite ha
    have hd : Continuous
        (torusScalarRepresentative
          (angularMollifiedPhysicalAdjointDriftCommutator W ℓ)) :=
      continuous_torusScalarRepresentative_of_periodic
        (continuous_angularMollifiedPhysicalAdjointDriftCommutator
          ha ha2 W ℓ)
        (TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic W ℓ)
    change Integrable
      (fun q : LogTorus n =>
        ‖torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
          (0 : ℂ)‖ ^ 2)
      ((angularWeightedTorusMeasure a).restrict S)
    have hi : IntegrableOn
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2)
        S (angularWeightedTorusMeasure a) :=
      (hd.norm.pow 2).continuousOn.integrableOn_compact hS
    change Integrable
      (fun q : LogTorus n =>
        ‖torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2)
      ((angularWeightedTorusMeasure a).restrict S) at hi
    refine hi.congr (Filter.Eventually.of_forall fun q => ?_)
    simp
  have hc : Tendsto
      (fun ℓ : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
            (sourceRadialCutoff m q : ℂ) • (0 : ℂ)‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) :=
    angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
      hlocal
      (by
        intro S hS
        simpa using
          angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
            ha ha2 W hS)
      m
  have ht := angularWeightedLp_tendsto_of_squared_error_integral
    (fun ℓ => angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m)
    (MeasureTheory.MemLp.zero :
      MemLp (fun _ : LogTorus n => (0 : ℂ)) 2
        (angularWeightedTorusMeasure a))
    (by simpa using hc)
  simpa using ht
end Ehrhart.TorusHomogeneousCutoffAdjoint
