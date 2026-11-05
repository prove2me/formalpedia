-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_grid_crossing_pair_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:27:37.321265+00:00
-- url     : https://prove2.me/submissions/945ada9c-95f4-4a56-a0ec-018045b47d1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source grid past/future marked times count precisely the crossing ordered pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (F.filter (fun u => u ≤ s)).card *
      (F.filter (fun u => s < u ∧ u ≤ t)).card =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  change (F.filter (fun u => u ≤ s)).card *
      (F.filter (fun u => s < u ∧ u ≤ t)).card =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card
  have hp : ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)) =
      (F.filter (fun u => u ≤ s)) ×ˢ
        (F.filter (fun u => s < u ∧ u ≤ t)) := by
    ext p
    rcases p with ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hp, Finset.card_product]
