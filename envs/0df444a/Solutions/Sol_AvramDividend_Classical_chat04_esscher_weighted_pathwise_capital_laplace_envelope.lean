-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_pathwise_capital_laplace_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:43:40.30335+00:00
-- url     : https://prove2.me/submissions/49fbb6fc-638d-4257-b49b-01318403c9c2

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_laplace_envelope_all_paths

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
    (t : ℝ≥0) (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω},
      Real.exp (-β * x) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) =
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
  rw [integral_mul_const]
  rw [pathwise_killed_survival_laplace_envelope_all_paths X t ω β hβ]
