-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:41:52.264209+00:00
-- url     : https://prove2.me/submissions/05c465aa-80b6-4c52-92dc-65e3969ea65e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Strictly downward jumps of a càdlàg path admit rational levels separating their left and right neighbourhoods. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hdown : Y t < Function.leftLim Y t)
    (hLeft : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hRight : ContinuousWithinAt Y (Ici t) t) :
    ∃ (a : ℚ) (s b : ℝ≥0), s < t ∧ t < b ∧
      (∀ u ∈ Ioo s t, (a : ℝ) < Y u) ∧
      (∀ u ∈ Ico t b, Y u < (a : ℝ)) := by
  obtain ⟨a, ha, hb⟩ := exists_rat_btwn hdown
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hEvL : ∀ᶠ u in 𝓝[<] t, (a : ℝ) < Y u :=
    hLeft.eventually (isOpen_Ioi.mem_nhds hb)
  obtain ⟨s, hs, hL⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset ht).mp hEvL
  have hEvR : ∀ᶠ u in 𝓝[≥] t, Y u < (a : ℝ) :=
    hRight.eventually (isOpen_Iio.mem_nhds ha)
  obtain ⟨b, hb', hR⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hEvR
  exact ⟨a, s, b, hs.2, hb', hL, hR⟩
