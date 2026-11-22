-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:07:44.534162+00:00
-- url     : https://prove2.me/submissions/ebfe583b-5fd2-417f-8c0c-5bd17d1f199c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_original_rightcont_stopped_gaussian_weighted_abs_increment_young
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτevents : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτevents).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hHI : Integrable H P)
    (hHZI : Integrable (fun ω => H ω * abs
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHZ2I : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P)
    (hσ : 0 < X.σ) (hh : 0 < h) :
    (∫ ω, H ω *
      abs (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) ≤
    X.σ * Real.sqrt (h : ℝ) * (∫ ω, H ω ∂P) := by
  let δ : ℝ := X.σ * Real.sqrt (h : ℝ)
  have hhReal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hδ : 0 < δ :=
    mul_pos hσ (Real.sqrt_pos.2 hhReal)
  have hδsq : δ ^ 2 = (h : ℝ) * X.σ ^ 2 := by
    dsimp [δ]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hhReal)]
    ring
  have hYoung :=
    avram_agentB_original_rightcont_stopped_gaussian_weighted_abs_increment_young
      X hν τ hτevents hτstop T hbounded h H hH hHglobal
      hHnonneg hHI hHZI hHZ2I δ hδ
  have hRewrite :
      ((h : ℝ) * X.σ ^ 2 + δ ^ 2) * (∫ ω, H ω ∂P) =
        (2 * δ) * (δ * (∫ ω, H ω ∂P)) := by
    rw [← hδsq]
    ring
  rw [hRewrite] at hYoung
  by_contra hBad
  have hStrict :
      δ * (∫ ω, H ω ∂P) <
        (∫ ω, H ω *
          abs (X.X (τ ω + h) ω - X.X (τ ω) ω -
            (h : ℝ) * X.c) ∂P) := lt_of_not_ge hBad
  have hPositive : 0 < (2:ℝ) * δ := by positivity
  have hMul := mul_lt_mul_of_pos_left hStrict hPositive
  exact (not_lt_of_ge hYoung) hMul

