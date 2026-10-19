-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.integral_coverWeightedMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/510439ee-9cad-451d-aa6a-aeb2661ec14f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_continuous_coverWeight
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeight_pos

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
    (ha : Continuous a)
    (F : TorusCharacters.LogSpace n → ℂ) :
    (∫ z : TorusCharacters.LogSpace n, F z
      ∂(coverWeightedMeasure a)) =
    ∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z * F z
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
  have hm : Measurable
      (fun z : TorusCharacters.LogSpace n =>
        ENNReal.ofReal (coverWeight a z)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_coverWeight ha).measurable
  have hf : ∀ᵐ z ∂(volume :
      Measure (TorusCharacters.LogSpace n)),
      ENNReal.ofReal (coverWeight a z) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold coverWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm hf]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with z
  change
    (ENNReal.ofReal (coverWeight a z)).toReal • F z =
      (coverWeight a z : ℂ) * F z
  rw [ENNReal.toReal_ofReal (coverWeight_pos a z).le,
    Complex.real_smul]
end Ehrhart.WeightedDolbeaultBochnerIdentity
