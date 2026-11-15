-- Prove2me | solution 1 for AvramDividend.Classical.avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:19:49.663962+00:00
-- url     : https://prove2.me/submissions/1a11300d-102f-4a21-99a0-248756f46b97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable σ)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    Measurable (fun ω => ((marked ω).card : ℝ)) ∧
    Integrable (fun ω => ((marked ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((marked ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
    min ((i : ℝ≥0) * Δ) (σ ω)
  have hMono : ∀ ω, Monotone (grid ω) := by
    intro ω i j hij
    change min ((i : ℝ≥0) * Δ) (σ ω) ≤
      min ((j : ℝ≥0) * Δ) (σ ω)
    gcongr
  have hGridMeas : ∀ i, Measurable (fun ω => grid ω i) := by
    intro i
    change Measurable (fun ω => min ((i : ℝ≥0) * Δ) (σ ω))
    exact measurable_const.min hσmeas
  have hHorizon : ∀ ω i, i ∈ Finset.range (m + 1) →
      grid ω (i + 1) ≤ (n : ℝ≥0) := by
    intro ω i hi
    change min (((i + 1 : ℕ) : ℝ≥0) * Δ) (σ ω) ≤ (n : ℝ≥0)
    exact (min_le_right _ _).trans (hσbound ω)
  simpa only [grid] using
    avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
      X hFinite n (n : ℝ≥0) le_rfl (Finset.range (m + 1))
      grid hMono hGridMeas hHorizon
