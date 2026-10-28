-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_capital_laplace_horizon_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:26:05.118346+00:00
-- url     : https://prove2.me/submissions/27e41ce4-d663-436f-81de-0618540c3138

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_lintegral_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-β * x)) *
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (θ * X.X u ω -
              (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
      ∂volume) ≤
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-β * x)) *
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
      ∂volume) := by
  apply lintegral_mono
  intro x
  exact mul_le_mul_of_nonneg_left
    (chat04_esscher_killed_survival_lintegral_antitone
      X θ hθ x t u htu) bot_le
