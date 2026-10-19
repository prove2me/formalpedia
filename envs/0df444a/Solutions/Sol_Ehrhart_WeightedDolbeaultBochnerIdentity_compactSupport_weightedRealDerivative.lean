-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.compactSupport_weightedRealDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/2ad6a596-d29b-4542-8d13-54718547d860

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : HasCompactSupport F)
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (weightedRealDerivative a F v) := by
  unfold weightedRealDerivative
  exact (hF.fderiv_apply ℝ v).sub hF.mul_right
end Ehrhart.WeightedDolbeaultBochnerIdentity
