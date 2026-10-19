-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_barPartial_hermitian_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/727f0781-5789-4598-9b99-b13e57d3b698

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_barPartial_integration_by_parts
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weightedAntiholomorphicDerivative_conj
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_conj

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
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate F z j * conj (G z)
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * conj (weightedHolomorphicDerivative a G j z)
      ∂(coverWeightedMeasure a)) := by
  have hGc : ContDiff ℝ 1 (fun z => conj (G z)) :=
    Complex.conjCLE.contDiff.comp hG
  have hcomp := compactSupport_conj hGcompact
  calc
    _ = -(∫ z : TorusCharacters.LogSpace n,
      F z *
        weightedAntiholomorphicDerivative
          a (fun w => conj (G w)) j z
      ∂(coverWeightedMeasure a)) :=
        weighted_barPartial_integration_by_parts ha hF hGc hcomp j
    _ = _ := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with z
      rw [weightedAntiholomorphicDerivative_conj ha hG z j]
end Ehrhart.WeightedDolbeaultBochnerIdentity
