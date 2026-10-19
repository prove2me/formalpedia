-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/e3b07e59-341d-4763-8541-b2738feb562c

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
    (hF : Differentiable ℝ F)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => conj (F w)) z) v =
      conj ((fderiv ℝ F z) v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    (hF z).hasFDerivAt).fderiv
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v) h
  change (fderiv ℝ (Complex.conjCLE ∘ F) z) v =
    conj ((fderiv ℝ F z) v)
  calc
    (fderiv ℝ (Complex.conjCLE ∘ F) z) v =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using hp
    _ = conj ((fderiv ℝ F z) v) := rfl
end Ehrhart.WeightedDolbeaultBochnerIdentity
