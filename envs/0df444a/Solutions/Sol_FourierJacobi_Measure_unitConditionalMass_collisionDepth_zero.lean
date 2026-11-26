-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_collisionDepth_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:08.14187+00:00
-- url     : https://prove2.me/submissions/dcd0fb77-62e5-4503-bdf4-f5fa86b7eadb

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt
import Theorems.Thm_FourierJacobi_Measure_collisionTail_measurableSet
import Theorems.Thm_FourierJacobi_Measure_collisionTail_subset_units
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_collisionTail
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_integralUnits
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
theorem _root_.solution :
    unitConditionalMass K (integralUnits K \ collisionTail K 1) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ Set.sdiff_subset,
    measureReal_sdiff (collisionTail_subset_units K (by omega))
      (collisionTail_measurableSet K 1),
    integersHaar_real_collisionTail, integersHaar_real_integralUnits, pow_one]
  field_simp
  ring
end FourierJacobi.Measure
