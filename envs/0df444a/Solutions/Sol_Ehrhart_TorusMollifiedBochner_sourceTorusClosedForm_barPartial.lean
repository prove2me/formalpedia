-- Prove2me | solution 1 for Ehrhart.TorusMollifiedBochner.sourceTorusClosedForm_barPartial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/0fc6bae0-b000-48dc-ad9e-21d3134f78a2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusMollifiedBochner_barPartial_barPartial_commute

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusMollifiedBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusDistributionBridge TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusMollifiedBochner
theorem _root_.solution
    {n : ℕ}
    {F : LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F) :
    ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial
          (fun z => barPartialCoordinate F z i) j q) := by
  intro q
  apply Matrix.IsSymm.ext
  intro i j
  exact barPartial_barPartial_commute hF _ j i
end Ehrhart.TorusMollifiedBochner
