-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.complexRealMultiplication_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/217c0782-9730-4437-898a-c92eb1a74ed6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution (z : ℂ) (r : ℝ) :
    complexRealMultiplication z r = (r : ℂ) * z := by
  simp [complexRealMultiplication, Complex.real_smul]
end Ehrhart.DolbeaultRegularity
