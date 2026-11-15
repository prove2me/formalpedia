-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:00:55.99968+00:00
-- url     : https://prove2.me/submissions/2c1a1193-d5f2-4acc-9dc7-97fda23908ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
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
    (n : ℕ) (hn : 0 < n) (s t : ℕ → ℕ → ℝ≥0)
    (hst : ∀ m i, i < m → s m i ≤ t m i)
    (hWidth : ∀ m i, i < m →
      (((t m i - s m i : ℝ≥0) : ℝ)) =
        (n : ℝ) / ((m : ℝ) + 1))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        let Z : ℝ := ((X.X (t m i) ω - X.X (s m i) ω) -
          ((t m i - s m i : ℝ≥0) : ℝ) * X.c) / X.σ
        if δ ≤ Z then Real.exp (θ * Z) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    ((X.X (t m i) ω - X.X (s m i) ω) -
      ((t m i - s m i : ℝ≥0) : ℝ) * X.c) / X.σ
  let F : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if δ ≤ Z m i ω then Real.exp (θ * Z m i ω) else 0
  have hZm (m i : ℕ) : Measurable (Z m i) := by
    have h0 : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    have h1 : Measurable (X.X (t m i)) :=
      (X.adapted (t m i)).mono (𝓕.le _) le_rfl
    exact ((h1.sub h0).sub measurable_const).div_const _
  have hInt : ∀ m i, i < m → Integrable (F m i) P := by
    intro m i hi
    simpa only [F,Z] using
      (avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
        X hν hσ (s m i) (t m i) (hst m i hi) θ δ hθ)
  have hPos (m i : ℕ) (ω : Ω) : 0 ≤ F m i ω := by
    dsimp [F]; split_ifs <;> positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc : (0 : ℝ) < 3 * δ^2 / (8 * (n : ℝ)) := by
    have hd : 0 < δ^2 := sq_pos_of_pos hδ
    positivity
  have hCell : ∀ m i, i < m →
      (∫ ω, F m i ω ∂P) ≤
      Real.exp (θ * δ / 2 + (n : ℝ) * θ^2 / 2 -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1)) := by
    intro m i hi
    simpa only [F,Z] using
      (avram_ga_a220_original_gaussian_mesh_one_cell_positive_exponential_chernoff
        X hν hσ n m hn (s m i) (t m i)
        (hst m i hi) (hWidth m i hi) θ δ hθ hδ (hZm m i))
  exact (avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
    P F (θ * δ / 2 + (n : ℝ) * θ^2 / 2)
    (3 * δ^2 / (8 * (n : ℝ))) hc hInt hPos hCell)
