-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:43:41.078592+00:00
-- url     : https://prove2.me/submissions/dd25f56f-9227-487d-865f-ac1f09fe5ef5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Real-valued original BV jump magnitudes are additive over adjacent intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) +
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hω
  intro s t hst
  let jump (u : ℝ≥0) : ℝ :=
    Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
  have hleft : Summable (fun u : ℝ≥0 =>
      if 0 < u ∧ u ≤ s then jump u else 0) :=
    (hω 0 s (show (0 : ℝ≥0) ≤ s from zero_le)).1
  have hright : Summable (fun u : ℝ≥0 =>
      if s < u ∧ u ≤ t then jump u else 0) := (hω s t hst).1
  have hpoint (u : ℝ≥0) :
      (if 0 < u ∧ u ≤ t then jump u else 0) =
        (if 0 < u ∧ u ≤ s then jump u else 0) +
        (if s < u ∧ u ≤ t then jump u else 0) := by
    by_cases hus : u ≤ s
    · have hut : u ≤ t := hus.trans hst
      have hnot : ¬ s < u := not_lt.mpr hus
      by_cases hpos : 0 < u
      · simp [hpos, hus, hut, hnot]
      · simp [hpos, hnot]
    · have hsu : s < u := lt_of_not_ge hus
      have hpos : 0 < u := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsu
      by_cases hut : u ≤ t
      · simp [hpos, hus, hsu, hut]
      · simp [hpos, hus, hsu, hut]
  change (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then jump u else 0) =
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then jump u else 0) +
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then jump u else 0)
  calc
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then jump u else 0) =
        tsum (fun u : ℝ≥0 =>
          (if 0 < u ∧ u ≤ s then jump u else 0) +
            (if s < u ∧ u ≤ t then jump u else 0)) := by
          apply tsum_congr
          intro u
          exact hpoint u
    _ = _ := hleft.tsum_add hright
