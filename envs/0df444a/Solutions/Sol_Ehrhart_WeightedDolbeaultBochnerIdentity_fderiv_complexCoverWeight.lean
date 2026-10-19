-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_complexCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/f1ffefd1-13c2-4d2f-b953-f4a88520be71

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
    (ha : ContDiff ℝ 1 a)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (complexCoverWeight a) z) v =
      -((fderiv ℝ a z) v : ℂ) * complexCoverWeight a z := by
  have hd : Differentiable ℝ (coverWeight a) :=
    (contDiff_coverWeight ha).differentiable (by simp)
  have he := DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hd z v
  have hra := (ha.differentiable (by simp) z).hasFDerivAt.neg.exp.fderiv
  have hrv := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℝ => D v) hra
  change
    (fderiv ℝ (fun w => (coverWeight a w : ℂ)) z) v =
      -((fderiv ℝ a z) v : ℂ) * (coverWeight a z : ℂ)
  change (fderiv ℝ (fun w => (coverWeight a w : ℂ)) z) v =
    ((fderiv ℝ (coverWeight a) z) v : ℂ) at he
  rw [he]
  change
    (fderiv ℝ (fun w => Real.exp (-a w)) z) v =
      _ at hrv
  simp only [_root_.smul_apply,
    _root_.neg_apply, smul_eq_mul] at hrv
  change
    ((fderiv ℝ (fun w => Real.exp (-a w)) z) v : ℂ) =
      -((fderiv ℝ a z) v : ℂ) * (Real.exp (-a z) : ℂ)
  rw [hrv]
  push_cast
  simp only [Pi.neg_apply, Complex.ofReal_neg]
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
