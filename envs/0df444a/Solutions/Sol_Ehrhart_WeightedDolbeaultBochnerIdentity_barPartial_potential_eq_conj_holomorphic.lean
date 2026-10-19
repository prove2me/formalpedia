-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_potential_eq_conj_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/377cc1a0-27aa-47f2-8018-574751a543aa

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_conj_eq_conj_holomorphic

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
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => (a w : ℂ)) z j =
      conj (holomorphicCoordinate (fun w => (a w : ℂ)) z j) := by
  have hcomplex : ContDiff ℝ 1 (fun w => (a w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  have h := barPartial_conj_eq_conj_holomorphic hcomplex z j
  simpa only [Complex.conj_ofReal] using h
end Ehrhart.WeightedDolbeaultBochnerIdentity
