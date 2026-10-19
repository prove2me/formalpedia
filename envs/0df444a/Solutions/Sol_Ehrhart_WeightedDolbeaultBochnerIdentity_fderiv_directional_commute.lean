-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.fderiv_directional_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/4a2b2fea-e258-4ba2-9bde-de20f974bf2c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_directional

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
    (fderiv ℝ
      (fun ζ : TorusCharacters.LogSpace n =>
        (fderiv ℝ F ζ) w) z) v := by
  rw [fderiv_directional hF z v w,
    fderiv_directional hF z w v]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v
end Ehrhart.WeightedDolbeaultBochnerIdentity
