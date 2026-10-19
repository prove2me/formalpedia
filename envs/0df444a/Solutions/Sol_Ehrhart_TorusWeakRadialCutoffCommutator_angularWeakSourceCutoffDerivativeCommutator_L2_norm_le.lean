-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialCutoffCommutator.angularWeakSourceCutoffDerivativeCommutator_L2_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/fa20fcc2-a682-44cd-a56d-c5b5065876e0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreConvergence_complexLp_norm_le_of_ae_norm_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakRadialCutoffCommutator
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreConvergence
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusWeakRadialCutoffCommutator
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
      W hC m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W‖ := by
  have hcmp := complexLp_norm_le_of_ae_norm_le
    (angularWeakSourceCutoffDerivativeCommutator_memLp W hC m)
    (MeasureTheory.Lp.memLp W)
    (C := ((m : ℝ) + 1)⁻¹ * C)
    (mul_nonneg (by positivity) hC₀)
    (by
      filter_upwards [] with q
      exact angularWeakSourceCutoffDerivativeCommutator_norm_le
        W hC m q)
  simpa using hcmp
end Ehrhart.TorusWeakRadialCutoffCommutator
