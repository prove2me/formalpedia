-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_eventual_uniform_grid_pair_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:10:29.598857+00:00
-- url     : https://prove2.me/submissions/6fb2255e-fd1a-4696-a646-7ee6fd3b4b0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_chronological_pair_cover
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_pair_card_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- Original negative-band physical chronological-pair counts equal fine grid counts eventually. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ᶠ k : ℕ in atTop,
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
        ∑ i : Fin (k + 1),
          ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
            p.1 ≤ (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) ∧
            (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) < p.2 ∧
            p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) *
              (T / ((k : ℝ≥0) + 1))))).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  obtain ⟨idx, hidx, hsep⟩ :=
    avram_p2_e_compensator_original_negative_band_uniform_cells_with_separation
      X ω T hT n
  filter_upwards [hsep] with k hk
  let δ : ℝ≥0 := T / ((k : ℝ≥0) + 1)
  have hidx' : ∀ u ∈ F, idx u k < k + 1 := by
    intro u hu
    exact Nat.lt_succ_of_le (hidx u hu k).1
  have hcell' : ∀ u ∈ F,
      ((idx u k : ℕ) : ℝ≥0) * δ < u ∧
      u ≤ (((idx u k + 1 : ℕ) : ℝ≥0) * δ) := by
    intro u hu
    exact (hidx u hu k).2
  have hcover := avram_p2_e_compensator_uniform_cell_chronological_pair_cover
    F δ (k + 1) (fun u => idx u k) hidx' hcell' hk
  have hdisj := avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
    (k + 1) δ
  exact avram_p2_e_compensator_uniform_grid_pair_card_sum
    F δ (k + 1) hcover hdisj
