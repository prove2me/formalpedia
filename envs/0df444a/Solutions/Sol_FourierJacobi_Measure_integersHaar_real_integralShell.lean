-- Prove2me | solution 1 for FourierJacobi.Measure.integersHaar_real_integralShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:02.313893+00:00
-- url     : https://prove2.me/submissions/235dd042-8e3b-4147-af8e-94d07f43d2ad

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Theorems.Thm_FourierJacobi_Measure_integersHaar_real_maximalIdeal_pow

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
    (integersHaar K).real (integralShell K n) =
      (1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ)⁻¹ ^ n := by
  rw [integralShell, measureReal_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet,
    integersHaar_real_maximalIdeal_pow, integersHaar_real_maximalIdeal_pow, pow_succ]
  ring
end FourierJacobi.Measure
