-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifierAdjoint.complexCoverWeight_mul_translatedDensityCancelledCoverKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/f26ed5c7-1a7b-4f43-b481-4be28ae71f43

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeight_pos

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
    (k : ℕ) (x y : LogSpace n) :
    complexCoverWeight (angularCoverPotential a) y *
      (translatedDensityCancelledCoverKernel a k x y : ℂ) =
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) : ℂ) := by
  unfold translatedDensityCancelledCoverKernel complexCoverWeight
  push_cast
  have hne : (coverWeight (angularCoverPotential a) y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coverWeight_pos (angularCoverPotential a) y).ne'
  field_simp
end Ehrhart.TorusClosedMollifierAdjoint
