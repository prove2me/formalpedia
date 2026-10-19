-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.integrable_of_continuous_compact_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/3333888f-4753-4b09-9d25-495ea3d48ea5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeightedMeasure_isLocallyFinite

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
    (ha : Continuous a)
    (hF : Continuous F)
    (hFcompact : HasCompactSupport F) :
    Integrable F (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha
  exact hF.integrable_of_hasCompactSupport hFcompact
end Ehrhart.WeightedDolbeaultBochnerIdentity
