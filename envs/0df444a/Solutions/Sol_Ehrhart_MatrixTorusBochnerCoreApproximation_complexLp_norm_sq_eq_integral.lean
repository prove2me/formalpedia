-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerCoreApproximation.complexLp_norm_sq_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/82dc4837-42b9-401b-aaef-5ec25fd847c6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerCoreApproximation
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerCoreApproximation
theorem _root_.solution
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (f : MeasureTheory.Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x : X, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re
        (@inner ℂ (MeasureTheory.Lp E 2 μ) _ f f) :=
      norm_sq_eq_re_inner f
    _ = RCLike.re
        (∫ x : X, @inner ℂ E _ (f x) (f x) ∂μ) := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ x : X,
        RCLike.re (@inner ℂ E _ (f x) (f x)) ∂μ :=
      (integral_re
        (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ x : X, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (norm_sq_eq_re_inner (f x)).symm
end Ehrhart.MatrixTorusBochnerCoreApproximation
