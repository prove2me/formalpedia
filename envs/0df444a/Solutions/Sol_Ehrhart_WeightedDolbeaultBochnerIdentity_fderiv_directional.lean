-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_directional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/a45d0e1e-9ff4-4d73-81e9-4456a65fd9fa

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
    (hF : ContDiff ℝ 2 F)
    (z v w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ζ : TorusCharacters.LogSpace n =>
        (fderiv ℝ F ζ) v) z) w =
      ((fderiv ℝ (fderiv ℝ F) z) w) v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp) |>.differentiableAt
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := v))
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D w) he
  simpa [ContinuousLinearMap.flip_apply] using hp
end Ehrhart.WeightedDolbeaultBochnerIdentity
