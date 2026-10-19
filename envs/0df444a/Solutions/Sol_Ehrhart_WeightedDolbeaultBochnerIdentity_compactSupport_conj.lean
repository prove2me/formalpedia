-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.compactSupport_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/f76cb69b-bc9a-4d6b-95ad-d2e5b923b83e

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : HasCompactSupport F) :
    HasCompactSupport (fun z => conj (F z)) := by
  refine hF.mono ?_
  intro z hz
  change conj (F z) ≠ 0 at hz
  change F z ≠ 0
  intro hzero
  apply hz
  rw [hzero, map_zero]
end Ehrhart.WeightedDolbeaultBochnerIdentity
