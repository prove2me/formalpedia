-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifierAdjoint.hasCompactSupport_translatedDensityCancelledCoverKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/b4d8483e-f2d7-40b4-a47e-0a73e5b19f6e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_hasCompactSupport

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusClosedMollifierAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusClosedMollifierAdjoint
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ)
    (k : ℕ) (x : LogSpace n) :
    HasCompactSupport (translatedDensityCancelledCoverKernel a k x) := by
  have hκ := (complexShrinkingBump (n := n) k).hasCompactSupport_normed
    (μ := (volume : Measure (LogSpace n)))
  have ht := translatedRealKernel_hasCompactSupport hκ x
  have hm : HasCompactSupport
      (fun y : LogSpace n =>
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) (x - y) *
        (coverWeight (angularCoverPotential a) y)⁻¹) := ht.mul_right
  have hkernel :
      translatedDensityCancelledCoverKernel a k x =
        (fun y : LogSpace n =>
          (complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) *
          (coverWeight (angularCoverPotential a) y)⁻¹) := by
    funext y
    exact div_eq_mul_inv _ _
  rw [hkernel]
  exact hm
end Ehrhart.TorusClosedMollifierAdjoint
