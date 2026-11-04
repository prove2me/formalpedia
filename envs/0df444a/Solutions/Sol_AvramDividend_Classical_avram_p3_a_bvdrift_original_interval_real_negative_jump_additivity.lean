-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:47:41.763044+00:00
-- url     : https://prove2.me/submissions/778ec358-c294-4cb3-bc33-b7e9138f86dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine source BV real negative-jump series is additive under
arbitrary subdivision of a bounded interval, on one full event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
      (∑' u : ℝ≥0,
        (if s < u ∧ u ≤ r then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) =
      (∑' u : ℝ≥0,
        (if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) +
      (∑' u : ℝ≥0,
        (if t < u ∧ u ≤ r then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum X hBV]
    with ω hω
  intro s t r hst htr
  let J (u : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
  have hleft : Summable (fun u : ℝ≥0 =>
      (if s < u ∧ u ≤ t then J u else 0).toReal) := by
    exact (hω s t hst).1
  have hright : Summable (fun u : ℝ≥0 =>
      (if t < u ∧ u ≤ r then J u else 0).toReal) := by
    exact (hω t r htr).1
  have hpoint (u : ℝ≥0) :
      (if s < u ∧ u ≤ r then J u else 0).toReal =
        (if s < u ∧ u ≤ t then J u else 0).toReal +
        (if t < u ∧ u ≤ r then J u else 0).toReal := by
    by_cases hut : u ≤ t
    · have hur : u ≤ r := hut.trans htr
      have hnot : ¬ t < u := not_lt.mpr hut
      by_cases hsu : s < u
      · simp [hsu, hut, hur, hnot]
      · simp [hsu, hnot]
    · have htu : t < u := lt_of_not_ge hut
      have hsu : s < u := lt_of_le_of_lt hst htu
      by_cases hur : u ≤ r
      · simp [hsu, hut, htu, hur]
      · simp [hsu, hut, htu, hur]
  change (∑' u : ℝ≥0, (if s < u ∧ u ≤ r then J u else 0).toReal) =
    (∑' u : ℝ≥0, (if s < u ∧ u ≤ t then J u else 0).toReal) +
    (∑' u : ℝ≥0, (if t < u ∧ u ≤ r then J u else 0).toReal)
  have hfun :
      (fun u : ℝ≥0 => (if s < u ∧ u ≤ r then J u else 0).toReal) =
      (fun u : ℝ≥0 =>
        (if s < u ∧ u ≤ t then J u else 0).toReal +
        (if t < u ∧ u ≤ r then J u else 0).toReal) := by
    funext u
    exact hpoint u
  have hsum := congrArg (fun f : ℝ≥0 → ℝ => ∑' u, f u) hfun
  exact hsum.trans (Summable.tsum_add hleft hright)
