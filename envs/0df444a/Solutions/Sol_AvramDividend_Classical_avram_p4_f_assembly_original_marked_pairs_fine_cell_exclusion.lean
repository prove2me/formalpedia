-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_fine_cell_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:16:30.20079+00:00
-- url     : https://prove2.me/submissions/cde25aca-754b-4c89-b70d-eba443c415a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
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
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        ∀ s t : ℝ, s < (u : ℝ) → (v : ℝ) ≤ t →
          (k : ℝ) * (t - s) ≤ (T : ℝ) → False := by
  dsimp only
  obtain ⟨k, hk, hgap⟩ :=
    avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale X ω T n
  refine ⟨k, hk, ?_⟩
  intro u hu v hv huv s t hsu hvt hwidth
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hle : (v : ℝ) - (u : ℝ) ≤ t - s := by linarith
  have hmul : (k : ℝ) * ((v : ℝ) - (u : ℝ)) ≤
      (k : ℝ) * (t - s) := mul_le_mul_of_nonneg_left hle hkR
  have hstrict := hgap u hu v hv huv
  have himp : (T : ℝ) < (T : ℝ) :=
    lt_of_lt_of_le hstrict (le_trans hmul hwidth)
  exact (lt_irrefl _) himp
