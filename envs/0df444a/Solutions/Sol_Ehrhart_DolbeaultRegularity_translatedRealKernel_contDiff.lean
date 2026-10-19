-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.translatedRealKernel_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/f42c563d-65f2-4e7f-bd11-6e43c4a4f9d1

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
    (hκ : ContDiff ℝ 1 κ)
    (x : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun t : TorusCharacters.LogSpace n => κ (x - t)) := by
  change ContDiff ℝ 1
    (κ ∘ (fun t : TorusCharacters.LogSpace n => x - t))
  exact hκ.comp (contDiff_const.sub contDiff_id)
end Ehrhart.DolbeaultRegularity
