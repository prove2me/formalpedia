-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.contDiff_complexCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/85eea487-b0f4-447a-b82f-d38e81f22eb7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_coverWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
namespace Ehrhart.WeightedDolbeaultBochnerIdentity
theorem _root_.solution {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a) :
    ContDiff ℝ 1 (complexCoverWeight a) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_coverWeight ha)
end Ehrhart.WeightedDolbeaultBochnerIdentity
