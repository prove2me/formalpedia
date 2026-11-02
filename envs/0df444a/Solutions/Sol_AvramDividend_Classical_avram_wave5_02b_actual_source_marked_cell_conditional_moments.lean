-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_marked_cell_conditional_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:51:56.739754+00:00
-- url     : https://prove2.me/submissions/d63ba56f-846e-4316-866f-dfd29dbd0b6b

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
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (hJint : Integrable
      (fun ω => J (fun t => X.X (s + t) ω - X.X s ω)) P)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P)
    (hFirst : (∫ ω, J (fun t => X.X (s + t) ω - X.X s ω) ∂P) = 0)
    (hSecond : (∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) =
      rate * ∫ z, f z ^ 2 ∂ν) :
    let Z : Ω → ℝ := fun ω =>
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν
    (P[Z | 𝓕 s] =ᵐ[P] fun _ => 0) ∧
      (P[(fun ω => Z ω ^ 2) | 𝓕 s] =ᵐ[P]
        fun _ => rate * ∫ z, f z ^ 2 ∂ν) := by
  have h := avram_wave5_02b_original_future_path_conditional_first_second_moments
    X s J hJ hJint hJ2int
  rw [hFirst, hSecond] at h
  dsimp only
  simpa only [hRep] using h
