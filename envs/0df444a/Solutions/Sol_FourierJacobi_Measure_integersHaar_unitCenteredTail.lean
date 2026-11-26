-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_unitCenteredTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:00.346021+00:00
-- url     : https://prove2.me/submissions/d55609ab-0de8-4e60-9c33-c21a496e52b8

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_maximalIdeal_pow
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
theorem _root_.solution (a : 𝒪[K]ˣ) (n : ℕ) :
    integersHaar K (unitCenteredTail K a n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  simp only [unitCenteredTail, sub_eq_add_neg, measure_preimage_add_right]
  exact integersHaar_maximalIdeal_pow K n
end FourierJacobi.Measure
