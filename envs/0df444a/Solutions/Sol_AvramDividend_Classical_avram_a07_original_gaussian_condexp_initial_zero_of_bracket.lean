-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_gaussian_condexp_initial_zero_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:25:43.907076+00:00
-- url     : https://prove2.me/submissions/046167cc-6580-41ec-bd0e-b01fefdb756b

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_gaussian_residual_initial_zero_of_bracket
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (R : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      P[R t | 𝓕.rightCont s] =ᵐ[P] R s)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ t : ℝ≥0, P[R t | 𝓕.rightCont 0] =ᵐ[P] (0 : Ω → ℝ) := by
  have hRzero :=
    avram_a07_original_gaussian_residual_initial_zero_of_bracket
      R a hRbracket
  intro t
  filter_upwards [hRmart 0 t zero_le, hRzero] with ω hmart hzero
  calc
    P[R t | 𝓕.rightCont 0] ω = R 0 ω := hmart
    _ = 0 := hzero
