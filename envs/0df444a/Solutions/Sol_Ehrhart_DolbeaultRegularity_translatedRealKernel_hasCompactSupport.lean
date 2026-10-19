-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.translatedRealKernel_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/00815c1f-da4b-4e70-a1fc-770ffa3e196b

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
theorem _root_.solution {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ)
    (x : TorusCharacters.LogSpace n) :
    HasCompactSupport
      (fun t : TorusCharacters.LogSpace n => κ (x - t)) := by
  simpa [Function.comp_def, Equiv.subLeft_apply] using
    hκ.comp_homeomorph (Homeomorph.subLeft x)
end Ehrhart.DolbeaultRegularity
