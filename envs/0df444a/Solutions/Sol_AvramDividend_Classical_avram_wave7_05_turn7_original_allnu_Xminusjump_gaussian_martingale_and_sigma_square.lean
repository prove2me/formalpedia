-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:05:37.405278+00:00
-- url     : https://prove2.me/submissions/b7b67189-70ed-4155-9f92-a7f2753a821e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Exact same-original-space Gaussian residual is a martingale with sigma squared compensated square. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Martingale M 𝓕.rightCont P ∧
      Martingale (fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2)
        𝓕.rightCont P := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hFun :
      M = (fun t ω => Y.X t ω - (t : ℝ) * Y.c) := by
    funext t ω
    exact hM t ω
  have hSquare :
      (fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2) =
      (fun t ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2 -
        (t : ℝ) * Y.σ ^ 2) := by
    funext t ω
    rw [hM t ω, hYσ]
  change Martingale M 𝓕.rightCont P ∧
    Martingale (fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2)
      𝓕.rightCont P
  constructor
  · rw [hFun]
    exact avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
      Y hYν
  · rw [hSquare]
    exact avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
      Y hYν
