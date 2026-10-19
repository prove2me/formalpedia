-- Prove2me | solution 1 for Ehrhart.TorusNoncompactBochner.complexScalar_integral_mul_conj_re_eq_L2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/719ef48d-c5af-4f3c-b240-a6d2e2544cbd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusNoncompactBochner
theorem _root_.solution
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {F : X → ℂ}
    (hF : MemLp F 2 μ) :
    (∫ x : X, F x * conj (F x) ∂μ).re =
      ‖hF.toLp F‖ ^ 2 := by
  have hre :
      (∫ x : X, F x * conj (F x) ∂μ) =
        ∫ x : X,
          @inner ℂ ℂ _ ((hF.toLp F) x) ((hF.toLp F) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply]
  rw [hre, ← MeasureTheory.L2.inner_def]
  change
    RCLike.re
      (@inner ℂ (MeasureTheory.Lp ℂ 2 μ) _
        (hF.toLp F) (hF.toLp F)) =
      ‖hF.toLp F‖ ^ 2
  exact (norm_sq_eq_re_inner (hF.toLp F)).symm
end Ehrhart.TorusNoncompactBochner
