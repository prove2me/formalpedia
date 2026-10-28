-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_true_capital_transform_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:33:05.6767+00:00
-- url     : https://prove2.me/submissions/3489f08a-6f57-405a-9729-ae35c536309f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_weight_inside_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_laplace_horizon_antitone
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
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X u ω -
                (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume) ≤
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume) := by
  calc
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-β * x) *
              Real.exp (θ * X.X u ω -
                (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P
      ∂volume) =
      (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-β * x)) *
        (∫⁻ ω,
          ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
            (fun ω => ENNReal.ofReal
              (Real.exp (θ * X.X u ω -
                (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
        ∂volume) := by
      apply lintegral_congr
      intro x
      exact chat04_esscher_capital_weight_inside_lintegral X x u β θ
    _ ≤
      (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-β * x)) *
        (∫⁻ ω,
          ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => ENNReal.ofReal
              (Real.exp (θ * X.X t ω -
                (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
        ∂volume) :=
      chat04_esscher_capital_laplace_horizon_antitone X θ β hθ hβ t u htu
    _ = _ := by
      apply lintegral_congr
      intro x
      exact (chat04_esscher_capital_weight_inside_lintegral X x t β θ).symm
