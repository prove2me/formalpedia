-- Prove2me | solution 1 for FourierJacobi.Measure.collisionTail_subset_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:57.242665+00:00
-- url     : https://prove2.me/submissions/72dcd261-eb45-4aad-9910-58b85cf20bc5

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    collisionTail K n ⊆ integralUnits K := by
  intro x hx
  have hm : x - 1 ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  intro hx'
  have h1 := (𝓂[K]).sub_mem hx' hm
  simp only [sub_sub_cancel] at h1
  exact Ideal.one_notMem 𝓂[K] h1
end FourierJacobi.Measure
