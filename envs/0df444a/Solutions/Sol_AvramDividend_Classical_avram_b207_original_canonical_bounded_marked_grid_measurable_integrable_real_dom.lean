-- Prove2me | solution 1 for AvramDividend.Classical.avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:59:06.636262+00:00
-- url     : https://prove2.me/submissions/c4aff795-3e84-4995-a44d-ebcbb68df1be

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

/-- Canonical actual source marked random-grid cardinal, measurable and integrable with real Poisson domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T)
 :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) ∧
    Integrable (fun ω => ((J ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) := by
  classical
  intro J
  have hCountMeas :=
    (avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
      X (fun _ : Ω => T) measurable_const).aemeasurable (μ := P)
  obtain ⟨hJM, hJdom⟩ :=
    avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
      X hFinite n T hT S grid hMono hGridMeas hHorizon hCountMeas
  have hJI : Integrable (fun ω => ((J ω).card : ℝ)) P :=
    (avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
      X hFinite T Set.univ J hJM hJdom).1
  exact ⟨hJM, hJI, hJdom⟩
