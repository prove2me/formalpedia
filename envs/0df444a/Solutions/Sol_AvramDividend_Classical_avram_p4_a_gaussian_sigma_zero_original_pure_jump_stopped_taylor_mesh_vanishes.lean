-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_original_pure_jump_stopped_taylor_mesh_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:37:28.102115+00:00
-- url     : https://prove2.me/submissions/c6efa002-a663-46b8-8475-5c8c2a873fc1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- In the zero-Gaussian-variance branch, an original-source pure-jump
decomposition makes every stopped Gaussian Taylor mesh vanish pathwise.
No auxiliary Brownian motion, stopping-time regularity or global C2 bound is
used; obtaining the pure-jump decomposition is a separate upstream task. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hPure : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let Z : ℝ≥0 → ℝ := fun u =>
        X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
      (∑ i ∈ S,
        (G i ω * (Z (τ i ω + h i) - Z (τ i ω)) +
          (1 / 2 : ℝ) * H i ω *
            ((Z (τ i ω + h i) - Z (τ i ω)) ^ 2 -
              (h i : ℝ) * X.σ ^ 2))) = 0 := by
  filter_upwards [hPure] with ω hω
  dsimp only
  apply Finset.sum_eq_zero
  intro i hi
  simp only [hω (τ i ω + h i), hω (τ i ω), hσ]
  push_cast
  ring
