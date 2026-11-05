-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:05:24.426373+00:00
-- url     : https://prove2.me/submissions/6902170f-017f-4460-bb57-0cf190b6883a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_times_chronological_gap
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
        (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ)) := by
  dsimp only
  obtain ⟨δ, hδ, hgap⟩ :=
    avram_p4_f_assembly_original_marked_times_chronological_gap X ω T n
  obtain ⟨k, hk⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  intro u hu v hv huv
  have hle := hgap u hu v hv huv
  have hk' : (T : ℝ) / δ < ((k + 1 : ℕ) : ℝ) := by
    exact lt_of_lt_of_le hk (by exact_mod_cast Nat.le_succ k)
  have ht : (T : ℝ) < ((k + 1 : ℕ) : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hk'
  exact lt_of_lt_of_le ht
    (mul_le_mul_of_nonneg_left hle (by positivity))
