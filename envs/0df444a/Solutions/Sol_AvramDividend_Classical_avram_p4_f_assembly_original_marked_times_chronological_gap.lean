-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_times_chronological_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:16:48.683987+00:00
-- url     : https://prove2.me/submissions/531f7604-d62b-4105-ab4f-a1ebd61a4e3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v → δ ≤ (v : ℝ) - (u : ℝ) := by
  dsimp only
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  obtain ⟨δ, hδ, hgap⟩ :=
    avram_wave7_06_finite_NNReal_marked_times_pairwise_gap F
  refine ⟨δ, hδ, ?_⟩
  intro u hu v hv huv
  have huv' : (u : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast (le_of_lt huv)
  have h := hgap u hu v hv (ne_of_lt huv)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv')] at h
  exact h
