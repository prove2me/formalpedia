-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_real_integralUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:22.586924+00:00
-- url     : https://prove2.me/submissions/7200569c-c942-42db-8e3a-ff20176dd18b

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_maximalIdeal_pow
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
    (integersHaar K).real (integralUnits K) = 1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [integralUnits, measureReal_compl
    (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet]
  simpa using congrArg (fun x : ℝ => 1 - x) (integersHaar_real_maximalIdeal_pow K 1)
end FourierJacobi.Measure
