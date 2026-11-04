-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:47:41.284227+00:00
-- url     : https://prove2.me/submissions/d51b2e39-34c0-4446-85e9-30d02bda555e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On every actual BV interval, the signed real source left-jump magnitudes
form a summable series equal to the full genuine ENNReal jump total. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 =>
        if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) ∧
      (∑' u : ℝ≥0,
        if s < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal =
        ∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0 := by
  filter_upwards [avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum X hBV] with ω hω
  intro s t hst
  obtain ⟨hsum, heq⟩ := hω s t hst
  have hpoint :
      (fun u : ℝ≥0 =>
        (if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) =
      (fun u : ℝ≥0 =>
        if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
    funext u
    by_cases hu : s < u ∧ u ≤ t
    · have hsnonneg : (0 : ℝ≥0) ≤ s := zero_le
      have hpos : 0 < u := lt_of_le_of_lt hsnonneg hu.1
      simpa [hu] using
        (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
          X ω u hpos).2
    · simp [hu]
  rw [hpoint] at hsum heq
  exact ⟨hsum, heq⟩
