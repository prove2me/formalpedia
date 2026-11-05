-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_source_ordered_pairs_as_past_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:12:32.660351+00:00
-- url     : https://prove2.me/submissions/ac5fd014-403f-4b5e-9009-e9bd24451681

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
      ∑ t ∈ F, (F.filter (fun u => u < t)).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  change ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
    ∑ t ∈ F, (F.filter (fun u => u < t)).card
  calc
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
        ∑ p ∈ (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2), (1 : ℕ) := by
      rw [Finset.card_eq_sum_ones]
    _ = ∑ u ∈ F, ∑ t ∈ F, if u < t then (1 : ℕ) else 0 := by
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ t ∈ F, ∑ u ∈ F, if u < t then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ F, (F.filter (fun u => u < t)).card := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_filter]
