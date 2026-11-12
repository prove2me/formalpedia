-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_gaussian_residual_martingale_mean_zero_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:21:31.957275+00:00
-- url     : https://prove2.me/submissions/61b5aa4c-dadc-4152-bd84-b327ad7627d6

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
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      P[R t | 𝓕.rightCont s] =ᵐ[P] R s)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * a ^ 2) :
    ∀ t : ℝ≥0, (∫ ω, R t ω ∂P) = 0 := by
  have hRzero :=
    avram_a07_original_gaussian_residual_initial_zero_of_bracket
      R a hRbracket
  intro t
  have hM := hRmart 0 t zero_le
  calc
    (∫ ω, R t ω ∂P) =
        (∫ ω, P[R t | 𝓕.rightCont 0] ω ∂P) := by
      exact (integral_condExp
        (m := 𝓕.rightCont 0) (μ := P) (f := R t)
        (𝓕.rightCont.le 0)).symm
    _ = (∫ ω, R 0 ω ∂P) := integral_congr_ae hM
    _ = (∫ _ : Ω, (0 : ℝ) ∂P) := integral_congr_ae hRzero
    _ = 0 := by simp
