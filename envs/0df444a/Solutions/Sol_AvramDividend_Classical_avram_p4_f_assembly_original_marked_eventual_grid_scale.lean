-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_eventual_grid_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:23:45.051178+00:00
-- url     : https://prove2.me/submissions/1fdce043-1fb9-41ce-9ac0-eec6d0a676c0

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

/-- All sufficiently fine deterministic meshes strictly separate original jump pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ u ∈ F, ∀ v ∈ F, u < v →
          (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by
  dsimp only
  obtain ⟨k₀, hk₀, hsep⟩ :=
    avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale X ω T n
  refine ⟨k₀, hk₀, ?_⟩
  intro k hk u hu v hv huv
  have huv' : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
  have hgap : 0 ≤ (v : ℝ) - (u : ℝ) :=
    sub_nonneg.mpr (le_of_lt huv')
  have hcast : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact lt_of_lt_of_le (hsep u hu v hv huv)
    (mul_le_mul_of_nonneg_right hcast hgap)
