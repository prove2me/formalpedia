-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:05.673585+00:00
-- url     : https://prove2.me/submissions/6fa044bf-2239-46f6-afb9-ba4f377e0adc

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_maximalIdeal_pow

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
    additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  rw [← integersHaar_apply, integersHaar_maximalIdeal_pow]
end FourierJacobi.Measure
