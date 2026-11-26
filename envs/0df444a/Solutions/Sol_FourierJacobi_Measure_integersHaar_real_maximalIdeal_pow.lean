-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_real_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:32.491024+00:00
-- url     : https://prove2.me/submissions/e99bee0d-1297-42fc-99b5-b159d42e5397

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
theorem _root_.solution (n : ℕ) :
    (integersHaar K).real ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) =
      (residueCardinality K : ℝ)⁻¹ ^ n := by
  simp [measureReal_def, integersHaar_maximalIdeal_pow]
end FourierJacobi.Measure
