-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_ruinclipped_finiteactivity_weighted_marked_grid_L1_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:36:19.28021+00:00
-- url     : https://prove2.me/submissions/6b714741-c27a-4525-9453-8fb895753535

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
import Theorems.Thm_AvramDividend_Classical_avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable σ)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ i ω, |W i ω| ≤ L) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    AEStronglyMeasurable (fun ω => ∑ i ∈ marked ω, W i ω) P →
    Integrable (fun ω => ∑ i ∈ marked ω, W i ω) P := by
  intro Δ grid marked hMeas
  have hCount :=
    avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
      X hFinite n m σ hσmeas hσbound
  dsimp only at hCount
  exact avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
    P marked hCount.2.1 W L hL hW hMeas
