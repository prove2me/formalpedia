-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.integrable_mul_weightedRealDerivative_coverWeightedMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/52fbb7c9-45cd-4647-b554-56ed2e2a4c56

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeightedMeasure_isLocallyFinite
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_continuous_weightedRealDerivative
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_weightedRealDerivative

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
theorem _root_.solution
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        F z * weightedRealDerivative a G v z)
      (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha.continuous
  exact (hF.continuous.mul
    (continuous_weightedRealDerivative ha hG v)).integrable_of_hasCompactSupport
      (compactSupport_weightedRealDerivative hGcompact v).mul_left
end Ehrhart.WeightedDolbeaultBochnerIdentity
