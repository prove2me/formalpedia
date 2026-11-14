-- Prove2me | solution 1 for AvramDividend.Classical.avram_b183_original_true_marked_bounded_random_grid_real_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:58:38.0972+00:00
-- url     : https://prove2.me/submissions/e08a3795-71c9-4dd2-86b0-9ef7697f6b7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
import Theorems.Thm_AvramDividend_Classical_avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The real number of exact original physical negative-jump occupied cells in any bounded measurable random monotone stopped grid is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (S : Finset ℕ)
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Integrable (fun ω => ((J ω).card : ℝ)) P := by
  intro J
  classical
  have hCountMeas :=
    (avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
      X (fun _ : Ω => T) measurable_const).aemeasurable (μ := P)
  obtain ⟨hJM, hJdom⟩ :=
    avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
      X hFinite n T hT S grid hMono hGridMeas hHorizon hCountMeas
  exact (avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
    X hFinite T Set.univ J hJM hJdom).1
