-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_potential_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/4256fd7e-cd96-4ab9-81ee-693ba111a828

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (ha : ContDiff ℝ 1 a)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => (a w : ℂ)) z) v =
      ((fderiv ℝ a z) v : ℂ) :=
  DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    (ha.differentiable (by simp)) z v
end Ehrhart.WeightedDolbeaultBochnerIdentity
