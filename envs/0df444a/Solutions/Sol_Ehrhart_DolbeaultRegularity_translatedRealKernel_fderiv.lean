-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.translatedRealKernel_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/6d96fd25-4dc0-45a7-8f41-df1bc4668b58

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
    (x t v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun y : TorusCharacters.LogSpace n => κ (x - y)) t) v =
      -(fderiv ℝ κ (x - t)) v := by
  have hinner :
      HasFDerivAt
        (fun y : TorusCharacters.LogSpace n => x - y)
        (-(ContinuousLinearMap.id ℝ
          (TorusCharacters.LogSpace n))) t := by
    simpa using
      (hasFDerivAt_const (𝕜 := ℝ) x t).sub
        (hasFDerivAt_id (𝕜 := ℝ) t)
  have houter : DifferentiableAt ℝ κ (x - t) :=
    (hκ.differentiable (by simp)).differentiableAt
  have hchain := houter.hasFDerivAt.comp t hinner
  have heval := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℝ => D v)
      hchain.fderiv
  simpa [Function.comp_def] using heval
end Ehrhart.DolbeaultRegularity
