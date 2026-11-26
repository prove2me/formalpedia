-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_collisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:37.791285+00:00
-- url     : https://prove2.me/submissions/e48c4c88-9ca7-4ac0-96bb-2554c5dd928c

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt
import Theorems.Thm_FourierJacobi_Measure_collisionTail_measurableSet
import Theorems.Thm_FourierJacobi_Measure_collisionTail_succ_subset
import Theorems.Thm_FourierJacobi_Measure_collisionTail_subset_units
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_collisionTail
import Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_of_subset

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1) \ collisionTail K (n + 2)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (Set.Subset.trans Set.sdiff_subset (collisionTail_subset_units K (Nat.succ_pos n))),
    measureReal_sdiff (collisionTail_succ_subset K (n + 1))
      (collisionTail_measurableSet K (n + 2)),
    integersHaar_real_collisionTail, integersHaar_real_collisionTail]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  have hd : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 := by
    have hq0 : (residueCardinality K : ℝ) ≠ 0 := (lt_trans zero_lt_one hq).ne'
    have heq : 1 - (residueCardinality K : ℝ)⁻¹ =
        (residueCardinality K - 1) / residueCardinality K := by field_simp
    rw [heq]
    exact div_ne_zero (sub_ne_zero.mpr hq.ne') hq0
  calc
    _ = (residueCardinality K : ℝ)⁻¹ ^ (n + 1) *
        (1 - (residueCardinality K : ℝ)⁻¹) /
        (1 - (residueCardinality K : ℝ)⁻¹) := by congr 1; ring
    _ = _ := mul_div_cancel_right₀ _ hd
end FourierJacobi.Measure
