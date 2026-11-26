-- Prove2me | solution 1 for FourierJacobi.Measure.unitCenteredTail_subset_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:13.016491+00:00
-- url     : https://prove2.me/submissions/95a4e4cc-ccc4-46e4-b492-3143bc034931

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_mem_integralUnits_iff
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
theorem _root_.solution (a : 𝒪[K]ˣ) {n : ℕ} (hn : 0 < n) :
    unitCenteredTail K a n ⊆ integralUnits K := by
  intro x hx hx'
  have hm : x - (a : 𝒪[K]) ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  have ha : (a : 𝒪[K]) ∈ integralUnits K :=
    (mem_integralUnits_iff K _).mpr a.isUnit
  apply ha
  simpa using (𝓂[K]).sub_mem hx' hm
end FourierJacobi.Measure
