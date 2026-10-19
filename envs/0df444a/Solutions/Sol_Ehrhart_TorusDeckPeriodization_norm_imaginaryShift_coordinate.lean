-- Prove2me | solution 1 for Ehrhart.TorusDeckPeriodization.norm_imaginaryShift_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/2be8f286-aa1e-4055-89b7-fea7561d7c25

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckPeriodization
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckPeriodization
theorem _root_.solution
    {n : ℕ} (q : Fin n → ℤ) (i : Fin n) :
    ‖TorusCharacters.imaginaryShift q i‖ =
      |(q i : ℝ)| * (2 * Real.pi) := by
  simp [TorusCharacters.imaginaryShift,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
end Ehrhart.TorusDeckPeriodization
