-- Prove2me | solution 1 for FourierJacobi.Measure.collisionTail_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:25.099194+00:00
-- url     : https://prove2.me/submissions/5d18b8e8-4a98-4cc5-8b7d-0232fe0e3482

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar

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
theorem _root_.solution (n : ℕ) : MeasurableSet (collisionTail K n) :=
  (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet.preimage
    (by fun_prop)
end FourierJacobi.Measure
