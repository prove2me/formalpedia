-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_integralShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:56.871354+00:00
-- url     : https://prove2.me/submissions/6f87642e-2316-4f69-a73d-0cb1c1a2d606

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
    integersHaar K (integralShell K n) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n -
        (residueCardinality K : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  rw [integralShell, measure_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet.nullMeasurableSet
    (measure_ne_top _ _), integersHaar_maximalIdeal_pow, integersHaar_maximalIdeal_pow]
end FourierJacobi.Measure
