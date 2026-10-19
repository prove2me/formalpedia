-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerCoreConvergence.complexLp_norm_le_of_ae_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/6282c8b5-dda6-4e08-a083-321bf5db3618

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerCoreConvergence
open Set Function MeasureTheory Filter Matrix
open WeightedBrascampLieb EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerCoreConvergence
theorem _root_.solution
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : X → E} {g : X → F}
    (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x : X ∂μ, ‖f x‖ ≤ C * ‖g x‖) :
    ‖hf.toLp f‖ ≤ C * ‖hg.toLp g‖ := by
  have hsemi :=
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      hbound (2 : ℝ≥0∞)
  have htop :
      ENNReal.ofReal C * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  calc
    ‖hf.toLp f‖ = (eLpNorm f 2 μ).toReal :=
      MeasureTheory.Lp.norm_toLp f hf
    _ ≤ (ENNReal.ofReal C * eLpNorm g 2 μ).toReal :=
      ENNReal.toReal_mono htop hsemi
    _ = C * (eLpNorm g 2 μ).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    _ = C * ‖hg.toLp g‖ := by
      rw [MeasureTheory.Lp.norm_toLp g hg]
end Ehrhart.MatrixTorusBochnerCoreConvergence
