-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_predictable_cell_conditional_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:00:12.69853+00:00
-- url     : https://prove2.me/submissions/026b9652-61c8-4311-815c-9aa32bb0d7d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (C : Set ℝ) (f : ℝ → ℝ) (ν : Measure ℝ) (rate : ℝ)
    (H Z : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hH2 : StronglyMeasurable[𝓕 s] (fun ω => H ω ^ 2))
    (hZsource : ∀ ω, Z ω =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) = Z ω)
    (hZi : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hHZi : Integrable (H * Z) P)
    (hH2Z2i : Integrable (fun ω => H ω ^ 2 * Z ω ^ 2) P)
    (hFirst : (∫ ω, Z ω ∂P) = 0)
    (hSecond : (∫ ω, Z ω ^ 2 ∂P) = rate * ∫ z, f z ^ 2 ∂ν) :
    (P[H * Z | 𝓕 s] =ᵐ[P] fun _ => 0) ∧
    (P[(fun ω => (H ω * Z ω) ^ 2) | 𝓕 s] =ᵐ[P]
      fun ω => H ω ^ 2 * (rate * ∫ z, f z ^ 2 ∂ν)) := by
  have hJi : Integrable
      (fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) P := by
    simpa only [hRep] using hZi
  have hJ2i : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P := by
    simpa only [hRep] using hZ2i
  have hc := avram_wave5_02b_original_future_path_conditional_first_second_moments
    X s J hJ hJi hJ2i
  have hz : P[Z | 𝓕 s] =ᵐ[P] fun _ => 0 := by
    simpa only [hRep, hFirst] using hc.1
  have hz2 : P[(fun ω => Z ω ^ 2) | 𝓕 s] =ᵐ[P]
      fun _ => rate * ∫ z, f z ^ 2 ∂ν := by
    simpa only [hRep, hSecond] using hc.2
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hHZi hZi
  have hpull2 := condExp_mul_of_stronglyMeasurable_left hH2 hH2Z2i hZ2i
  have hProdEq : ((fun ω => H ω ^ 2) * (fun ω => Z ω ^ 2)) =
      (fun ω => (H ω * Z ω) ^ 2) := by
    funext ω
    simp only [Pi.mul_apply, mul_pow]
  rw [hProdEq] at hpull2
  constructor
  · filter_upwards [hpull, hz] with ω hω hzω
    simp only [Pi.mul_apply, hzω, mul_zero] at hω
    exact hω
  · filter_upwards [hpull2, hz2] with ω hω hzω
    simpa only [Pi.mul_apply, hzω] using hω
