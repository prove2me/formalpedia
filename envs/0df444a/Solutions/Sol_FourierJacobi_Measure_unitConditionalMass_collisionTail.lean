-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_collisionTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:04.735202+00:00
-- url     : https://prove2.me/submissions/e90eb3a3-6906-4b39-b129-2566bb6cb097

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt
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
    unitConditionalMass K (collisionTail K (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ (collisionTail_subset_units K (Nat.succ_pos n)),
    integersHaar_real_collisionTail, pow_succ]
  field_simp
end FourierJacobi.Measure
