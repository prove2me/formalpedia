-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_source_finite_cell_pairs_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:53:13.644421+00:00
-- url     : https://prove2.me/submissions/e7b5238a-c662-4519-bc64-caef1c5db9a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_source_marked_cell_order_embedding
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A physical source finite mesh exactly accounts for chronological jump pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
      (∑ i : Fin (k + 1),
        (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  obtain ⟨k, hk, g, horder⟩ :=
    avram_p4_f_assembly_original_source_marked_cell_order_embedding X ω T hT n
  change ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
    (∑ i : Fin (k + 1),
      (F.filter (fun u => g u < i)).card *
      (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  refine ⟨k, hk, g, ?_⟩
  exact avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
    X ω T n F rfl (k + 1) g horder
