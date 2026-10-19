-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.continuous_unweightedSourceTorusIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/c0cf4c30-dad7-4474-b4de-b4ac2196091e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (unweightedSourceTorusIntegrand φ f) := by
  unfold unweightedSourceTorusIntegrand
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul hf
end Ehrhart.MatrixTorusBochnerBridge
