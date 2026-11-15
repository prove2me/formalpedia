-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:31:24.171391+00:00
-- url     : https://prove2.me/submissions/da2799fa-af3a-4d2d-bf7b-f950d216c49b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro Δ s R
  have hInt := avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
    X hν hσ n θ δ hθ
  exact avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
    X hν hσ n hn θ δ hθ hδ hInt.1 hInt.2
