-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weightedAntiholomorphicDerivative_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/02657b4f-4956-46ae-b5bf-1eaa54767e5e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_conj_eq_conj_holomorphic
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_potential_eq_conj_holomorphic

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
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedAntiholomorphicDerivative a (fun w => conj (F w)) j z =
      conj (weightedHolomorphicDerivative a F j z) := by
  unfold weightedAntiholomorphicDerivative weightedHolomorphicDerivative
  rw [barPartial_conj_eq_conj_holomorphic hF z j,
    barPartial_potential_eq_conj_holomorphic ha z j]
  simp only [map_sub, map_mul]
end Ehrhart.WeightedDolbeaultBochnerIdentity
