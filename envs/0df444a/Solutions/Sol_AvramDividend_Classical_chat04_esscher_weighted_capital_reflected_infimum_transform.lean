-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_capital_reflected_infimum_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:14:00.252841+00:00
-- url     : https://prove2.me/submissions/6127866d-a86f-4dcf-bbb1-305baf5a1330

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_joint_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_inner_lintegral
import Mathlib.Analysis.Complex.Exponential

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
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω),
      ENNReal.ofReal
        (Real.exp (-β * max 0
          (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ∂P) := by
  calc
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
      (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
        Set.indicator
          {p : ℝ × Ω | 0 < p.1 ∧
            ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
          (fun p => ENNReal.ofReal
            (Real.exp (-β * p.1) *
              Real.exp (θ * X.X t p.2 -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
          (x, ω) ∂volume ∂P) :=
        chat04_esscher_weighted_killed_survival_joint_tonelli X t β θ
    _ = _ := by
      apply lintegral_congr
      intro ω
      exact chat04_esscher_weighted_killed_survival_inner_lintegral
        X t ω β θ hβ
