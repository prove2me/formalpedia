-- Prove2me | solution 1 for FourierJacobi.Measure.unitConditionalMass_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:16.367904+00:00
-- url     : https://prove2.me/submissions/268001b1-a8c6-40e6-9e2a-fd591ba40472

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_singleton
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



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
theorem _root_.solution (x : 𝒪[K]) : unitConditionalMass K {x} = 0 := by
  have h : integersHaar K ({x} ∩ integralUnits K) = 0 :=
    measure_mono_null Set.inter_subset_left (integersHaar_singleton K x)
  simp [unitConditionalMass, measureReal_def, h]
end FourierJacobi.Measure
