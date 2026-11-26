-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:02.543801+00:00
-- url     : https://prove2.me/submissions/70d2e0cd-2b9e-4ed3-953c-8f2f16af8cae

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_integralUnits

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
theorem _root_.solution (s : Set 𝒪[K]) (hs : s ⊆ integralUnits K) :
    unitConditionalMass K s = (integersHaar K).real s /
      (1 - (residueCardinality K : ℝ)⁻¹) := by
  rw [unitConditionalMass, Set.inter_eq_self_of_subset_left hs,
    integersHaar_real_integralUnits]
end FourierJacobi.Measure
