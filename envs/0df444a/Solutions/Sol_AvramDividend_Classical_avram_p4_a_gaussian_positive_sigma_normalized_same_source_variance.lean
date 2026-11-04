-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:50:06.686463+00:00
-- url     : https://prove2.me/submissions/3e93289a-a369-40a3-92da-7b59db4ee037

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- With a proven same-path Gaussian/jump decomposition and positive source
Gaussian coefficient, the normalised original residual has unit variance rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ) (t : ℝ≥0) :
    (∫ ω, ((X.X t ω - (t : ℝ) * X.c -
      Jsmall t ω - Jlarge t ω) / X.σ) ^ 2 ∂P) = (t : ℝ) := by
  have hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | (0 : ℝ≥0) ≤ s} := by
    intro s
    simp
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events (fun _ : Ω => (0 : ℝ≥0)) hτ
  have hVar : (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) =
      (t : ℝ) * Y.σ ^ 2 := by
    simpa [Y.X_zero] using
      (avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
        Y hYν (fun _ : Ω => (0 : ℝ≥0)) hτstop 0
        (by intro ω; simp) t)
  have hFn :
      (fun ω : Ω => ((X.X t ω - (t : ℝ) * X.c -
        Jsmall t ω - Jlarge t ω) / X.σ) ^ 2) =
      (fun ω : Ω => (X.σ ^ 2)⁻¹ * (Y.X t ω - (t : ℝ) * Y.c) ^ 2) := by
    funext ω
    rw [hSourceDecomp t ω]
    ring
  rw [hFn, integral_const_mul, hVar, hYσ]
  field_simp [ne_of_gt hσ]
