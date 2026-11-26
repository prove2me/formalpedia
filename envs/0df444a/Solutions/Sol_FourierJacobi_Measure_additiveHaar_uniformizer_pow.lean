-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:47:55.21013+00:00
-- url     : https://prove2.me/submissions/31fe56fe-fb2b-4f39-9f0a-6605022fc3a9

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_maximalIdeal_pow
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
theorem _root_.solution (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) :
    additiveHaar K ((fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have heq : (fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ =
      (fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := by
    rw [hπ, Ideal.span_singleton_pow]
    ext x
    constructor
    · rintro ⟨u, _, rfl⟩
      exact ⟨π ^ n * u, Ideal.mem_span_singleton.mpr ⟨u, rfl⟩, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hy
      exact ⟨u, Set.mem_univ _, by simp⟩
  rw [heq, additiveHaar_maximalIdeal_pow]
end FourierJacobi.Measure
