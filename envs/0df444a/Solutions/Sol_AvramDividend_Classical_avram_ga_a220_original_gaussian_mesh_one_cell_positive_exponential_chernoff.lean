-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:51:50.655209+00:00
-- url     : https://prove2.me/submissions/80b1c712-999a-40d9-930f-14716fbff84e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
import Theorems.Thm_AvramDividend_Classical_avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
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
    (n m : ℕ) (hn : 0 < n) (s t : ℝ≥0) (hst : s ≤ t)
    (hWidth : (((t - s : ℝ≥0) : ℝ)) =
      (n : ℝ) / ((m : ℝ) + 1))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hMeas : Measurable (fun ω : Ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) :
    (∫ ω, if δ ≤
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
      then Real.exp (θ *
        (((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
      else 0 ∂P) ≤
      Real.exp (θ * δ / 2 + (n : ℝ) * θ^2 / 2 -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1)) := by
  let Z : Ω → ℝ := fun ω =>
    ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
  have hr : 0 ≤ δ * ((m : ℝ) + 1) / (2 * (n : ℝ)) := by
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hBound := avram_ga_a69_original_gaussian_positive_tail_unconditional_expected_chernoff
    X hν hσ s t hst Z rfl hMeas θ
    (δ * ((m : ℝ) + 1) / (2 * (n : ℝ))) δ hθ hr
  change (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
    Real.exp (- (δ * ((m : ℝ) + 1) / (2 * (n : ℝ))) * δ +
      (((t - s : ℝ≥0) : ℝ)) *
      (θ + δ * ((m : ℝ) + 1) / (2 * (n : ℝ)))^2 / 2) at hBound
  rw [hWidth] at hBound
  exact hBound.trans (Real.exp_le_exp.mpr
    (avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
      n m hn θ δ))
