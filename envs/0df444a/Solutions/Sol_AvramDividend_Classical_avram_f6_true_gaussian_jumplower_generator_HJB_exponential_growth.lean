-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:44:50.97074+00:00
-- url     : https://prove2.me/submissions/a77362dc-4210-48b7-8f3b-0b9ce965f6b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_scalar_ode_exponential_growth
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (r : ℝ) (hr : 0 ≤ r)
    (hJumpLower : ∀ y : ℝ, 0 < y →
      -r * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  have ha : 0 < X.σ ^ 2 / 2 := by positivity
  have hqeff : 0 < q + r := by linarith
  apply avram_p4_f4_turn16_scalar_ode_exponential_growth
    (X.σ ^ 2 / 2) X.c (q + r) w C ha hqeff hTop
    hw0 hwcont hwneg hwsmooth
  intro y hy hCy
  have hg := (hwgen y hy hCy).2
  have hj := hJumpLower y hy
  dsimp [SpectrallyNegativeLevy.generator] at hg
  linarith
