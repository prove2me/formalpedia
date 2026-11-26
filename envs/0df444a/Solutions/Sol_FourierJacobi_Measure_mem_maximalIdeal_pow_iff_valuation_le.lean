-- Prove2me | solution 1 for FourierJacobi.Measure.mem_maximalIdeal_pow_iff_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:09.310087+00:00
-- url     : https://prove2.me/submissions/bb4faa04-afab-412e-bcaf-de324ce9de6c

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
theorem _root_.solution (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) (x : 𝒪[K]) :
    x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (π : K) ^ n := by
  rw [hπ, Ideal.span_singleton_pow]
  change x ∈ (Ideal.span {π ^ n} : Set 𝒪[K]) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  simp
end FourierJacobi.Measure
