-- Prove2me | solution 1 for FourierJacobi.Measure.residueCardinality_isPrimePow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:04.572341+00:00
-- url     : https://prove2.me/submissions/452e9cae-05a8-4206-8094-cbe4932053ec

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
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
omit [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution : IsPrimePow (residueCardinality K) := by
  let := Fintype.ofFinite 𝓀[K]
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (FiniteField.isPrimePow_card (K := 𝓀[K]))
end FourierJacobi.Measure
