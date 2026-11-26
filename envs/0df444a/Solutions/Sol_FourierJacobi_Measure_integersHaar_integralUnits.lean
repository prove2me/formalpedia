-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_integralUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:54.990907+00:00
-- url     : https://prove2.me/submissions/0c3f742f-9bba-4fa8-8685-74c04f0a8548

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
theorem _root_.solution :
    integersHaar K (integralUnits K) = 1 - (residueCardinality K : ℝ≥0∞)⁻¹ := by
  rw [integralUnits, measure_compl (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet
    (measure_ne_top _ _)]
  simpa using congrArg (fun x : ℝ≥0∞ => 1 - x) (integersHaar_maximalIdeal_pow K 1)
end FourierJacobi.Measure
