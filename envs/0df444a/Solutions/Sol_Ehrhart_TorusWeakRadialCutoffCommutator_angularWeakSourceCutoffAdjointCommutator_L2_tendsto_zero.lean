-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialCutoffCommutator.angularWeakSourceCutoffAdjointCommutator_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/a2dfecb8-4ceb-44f8-9a12-fc856ab1eeaf

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedResolventConstantCore_inv_nat_add_one_tendsto_zero
import Theorems.Thm_Ehrhart_TorusWeakRadialCutoffCommutator_angularWeakSourceCutoffAdjointCommutator_L2_norm_le

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
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C) :
    Tendsto
      (fun m : ℕ =>
        (angularWeakSourceCutoffAdjointCommutator_memLp
          W hC m).toLp
            (angularWeakSourceCutoffAdjointCommutator W m))
      atTop
      (nhds
        (0 : angularWeightedScalarL2 a)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => angularWeakSourceCutoffAdjointCommutator_L2_norm_le
      W hC₀ hC m)
  have ht := inv_nat_add_one_tendsto_zero.mul_const
    (C * ‖W‖)
  simpa [mul_assoc] using ht
end Ehrhart.TorusWeakRadialCutoffCommutator
