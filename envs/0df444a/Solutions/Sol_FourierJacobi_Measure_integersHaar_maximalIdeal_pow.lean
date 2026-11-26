-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:19.858591+00:00
-- url     : https://prove2.me/submissions/0278a248-4996-4022-ad1b-f2659e423b4e

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
theorem _root_.solution (n : ℕ) :
    integersHaar K ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have h := (𝓂[K] ^ n).toAddSubgroup.index_mul_measure
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet (integersHaar K)
  rw [maximalIdeal_pow_index, integersHaar_univ, Nat.cast_pow] at h
  rw [← ENNReal.inv_pow, ← one_div]
  exact (ENNReal.eq_div_iff (pow_ne_zero n (by exact_mod_cast
    (residueCardinality_pos K).ne')) (by finiteness)).mpr h
end FourierJacobi.Measure
