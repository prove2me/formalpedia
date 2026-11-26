-- Prove2me | solution 1 for FourierJacobi.Measure.valuation_ratio_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:07.134841+00:00
-- url     : https://prove2.me/submissions/e21fbaff-ee08-4031-8ca8-2cd18b537161

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (a x : 𝒪[K]) (hx : IsUnit x) :
    valuation K ((a : K) / (x : K) - 1) = valuation K ((x : K) - (a : K)) := by
  have hvx : valuation K (x : K) = 1 := by
    change valuation K ((algebraMap 𝒪[K] K) x) = 1
    exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hx
  have hx0 : (x : K) ≠ 0 := by
    intro h
    simp [h] at hvx
  have heq : (a : K) / (x : K) - 1 = ((a : K) - (x : K)) / (x : K) := by
    field_simp
  rw [heq, map_div₀, hvx, div_one, (valuation K).map_sub_swap]
end FourierJacobi.Measure
