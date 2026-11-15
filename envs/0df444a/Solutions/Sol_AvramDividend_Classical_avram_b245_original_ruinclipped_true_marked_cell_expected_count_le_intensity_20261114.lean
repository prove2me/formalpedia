-- Prove2me | solution 1 for AvramDividend.Classical.avram_b245_original_ruinclipped_true_marked_cell_expected_count_le_intensity_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:29:03.275212+00:00
-- url     : https://prove2.me/submissions/2d3aac49-6734-4b55-abea-1a6a0a101e37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
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
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    (∫ ω, ((marked ω).card : ℝ) ∂P) ≤
      ((n : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
  intro Δ grid marked
  obtain ⟨hMeas, hInt, hDom⟩ :=
    avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
      X hFinite n m σ hσstop hσbound
  have hMean :=
    avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite (n : ℝ≥0) (Iio (0 : ℝ))
      measurableSet_Iio (Set.Subset.rfl)
  calc
    (∫ ω, ((marked ω).card : ℝ) ∂P) ≤
        (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u)))
          (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal ∂P) :=
      integral_mono_ae hInt hMean.1 hDom
    _ = ((n : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := hMean.2
