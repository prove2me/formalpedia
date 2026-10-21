-- Prove2me | solution 1 for AvramDividend.Classical.chat06_drifted_compound_levy_laplace_field
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:05:04.529832+00:00
-- url     : https://prove2.me/submissions/575aacdc-5d8e-4655-ab58-cd19566a1250

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramChat06

/-- Assemble the *exact* Laplace field of a compound-Poisson
SpectrallyNegativeLevy from (i) positive-time Poisson-mark count
moment and (ii) the explicit unit-drift Lévy triplet exponent.
Measurability and the pathwise upward drift cap alone discharge
the remaining integrability requirement for all θ≥0. -/
theorem compound_levy_laplace_integrability_and_value
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (ν : Measure ℝ) (t : ℝ≥0) (θ m : ℝ)
    (hθ : 0 ≤ θ)
    (hMeas : Measurable (fun ω =>
      (t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))
    (hCap : ∀ ω, (t : ℝ) +
      ∑ i ∈ Finset.range (N ω), Y i ω ≤ (t : ℝ))
    (hCount : (∫ ω, Real.exp (θ *
      ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
      Real.exp ((t : ℝ) * (m - 1)))
    (hTriplet : laplaceExponent 1 0 ν θ = θ + (m - 1)) :
    Integrable (fun ω => Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) P ∧
      (∫ ω, Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω)) ∂P) =
        Real.exp ((t : ℝ) * laplaceExponent 1 0 ν θ) := by
  have hZ : Measurable (fun ω => Real.exp (θ *
      ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) := by
    fun_prop
  have hInt : Integrable (fun ω => Real.exp (θ *
      ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) P := by
    apply Integrable.of_bound hZ.aestronglyMeasurable
      (Real.exp (θ * (t : ℝ)))
    filter_upwards [] with ω
    have hc : θ * ((t : ℝ) +
      ∑ i ∈ Finset.range (N ω), Y i ω) ≤ θ * (t : ℝ) :=
      mul_le_mul_of_nonneg_left (hCap ω) hθ
    have he := Real.exp_le_exp.mpr hc
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  refine ⟨hInt, ?_⟩
  have hPoint : (fun ω => Real.exp (θ *
      ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) =
    (fun ω => Real.exp (θ * (t : ℝ)) *
      Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω)) := by
    funext ω
    rw [mul_add, Real.exp_add]
  rw [hPoint, integral_const_mul, hCount, hTriplet, ← Real.exp_add]
  congr 1
  ring

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (ν : Measure ℝ) (t : ℝ≥0) (θ m : ℝ)
    (hθ : 0 ≤ θ)
    (hMeas : Measurable (fun ω =>
      (t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))
    (hCap : ∀ ω, (t : ℝ) +
      ∑ i ∈ Finset.range (N ω), Y i ω ≤ (t : ℝ))
    (hCount : (∫ ω, Real.exp (θ *
      ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
      Real.exp ((t : ℝ) * (m - 1)))
    (hTriplet : laplaceExponent 1 0 ν θ = θ + (m - 1)) :
    Integrable (fun ω => Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω))) P ∧
      (∫ ω, Real.exp (θ *
        ((t : ℝ) + ∑ i ∈ Finset.range (N ω), Y i ω)) ∂P) =
        Real.exp ((t : ℝ) * laplaceExponent 1 0 ν θ) := by
  exact compound_levy_laplace_integrability_and_value
    N Y ν t θ m hθ hMeas hCap hCount hTriplet
