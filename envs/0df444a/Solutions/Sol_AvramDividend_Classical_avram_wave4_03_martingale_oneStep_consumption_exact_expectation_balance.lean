-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:22:19.077267+00:00
-- url     : https://prove2.me/submissions/606cef66-1477-4da2-a604-821bfe05836f

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, M t ω * (B s ω - B t ω) ∂μ) =
      (∫ ω, B s ω * M s ω ∂μ) -
        (∫ ω, B t ω * M t ω ∂μ) := by
  have hBsm (u : ℝ≥0) : AEStronglyMeasurable (B u) μ :=
    ((hB u).mono (𝓕.le u) le_rfl).aestronglyMeasurable
  have hBnorm (u : ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖B u ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hBbound u ω).1]
    exact (hBbound u ω).2
  have hIntST : Integrable (fun ω => B s ω * M t ω) μ :=
    (hM.integrable t).bdd_mul (hBsm s) (hBnorm s)
  have hIntTT : Integrable (fun ω => B t ω * M t ω) μ :=
    (hM.integrable t).bdd_mul (hBsm t) (hBnorm t)
  have hpull :=
    condExp_mul_of_aestronglyMeasurable_left
      ((hB s).stronglyMeasurable.aestronglyMeasurable)
      hIntST (hM.integrable t)
  change μ[(fun ω => B s ω * M t ω) | 𝓕 s] =ᵐ[μ]
    (fun ω => B s ω * μ[M t | 𝓕 s] ω) at hpull
  have hcond :
      μ[(fun ω => B s ω * M t ω) | 𝓕 s] =ᵐ[μ]
        (fun ω => B s ω * M s ω) := by
    filter_upwards [hpull, hM.2 s t hst] with ω hp hm
    calc
      μ[(fun ω => B s ω * M t ω) | 𝓕 s] ω =
        B s ω * μ[M t | 𝓕 s] ω := hp
      _ = B s ω * M s ω := by rw [hm]
  have hEq :
      (∫ ω, B s ω * M t ω ∂μ) =
      (∫ ω, B s ω * M s ω ∂μ) := by
    calc
      (∫ ω, B s ω * M t ω ∂μ) =
          ∫ ω, μ[(fun ω => B s ω * M t ω) | 𝓕 s] ω ∂μ := by
        exact (integral_condExp (μ := μ) (m := 𝓕 s) (m₀ := mΩ)
          (f := fun ω => B s ω * M t ω) (𝓕.le s)).symm
      _ = (∫ ω, B s ω * M s ω ∂μ) :=
        integral_congr_ae hcond
  calc
    (∫ ω, M t ω * (B s ω - B t ω) ∂μ) =
        ∫ ω, (B s ω * M t ω - B t ω * M t ω) ∂μ := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, B s ω * M t ω ∂μ) -
          (∫ ω, B t ω * M t ω ∂μ) :=
      integral_sub hIntST hIntTT
    _ = (∫ ω, B s ω * M s ω ∂μ) -
          (∫ ω, B t ω * M t ω ∂μ) := by rw [hEq]
