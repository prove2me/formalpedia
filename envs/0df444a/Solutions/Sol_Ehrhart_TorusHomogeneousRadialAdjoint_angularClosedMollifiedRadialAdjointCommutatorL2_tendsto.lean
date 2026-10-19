-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/740da735-4d23-41f9-9844-e99da40e5c02

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularGraphMollifiedPhysicalField_compact_weighted_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousRadialAdjoint_angularClosedMollifiedRadialAdjointCommutatorL2_sub_norm_sq_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousRadialAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousRadialAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    {B : ℝ}
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRadialAdjointCommutatorL2
          ha W ℓ m)
      atTop
      (nhds
        ((angularWeakSourceCutoffAdjointCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffAdjointCommutator W m))) := by
  have hS := (sourceCutoffBarGradient_hasCompactSupport
    (n := n) m).isCompact
  have hlocal :=
    TorusHomogeneousCutoffAdjoint.angularGraphMollifiedPhysicalField_compact_weighted_L2_tendsto_zero
      ha W hS
  have hsq :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRadialAdjointCommutatorL2
              ha W ℓ m -
            (angularWeakSourceCutoffAdjointCommutator_memLp
              W hB m).toLp
                (angularWeakSourceCutoffAdjointCommutator W m)‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero (fun ℓ => sq_nonneg _)
      (fun ℓ =>
        angularClosedMollifiedRadialAdjointCommutatorL2_sub_norm_sq_le
          ha W ℓ m hB)
    simpa using hlocal.const_mul
      ((((m : ℝ) + 1)⁻¹ * B) ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa [Real.sqrt_sq_eq_abs] using hsq.sqrt
end Ehrhart.TorusHomogeneousRadialAdjoint
