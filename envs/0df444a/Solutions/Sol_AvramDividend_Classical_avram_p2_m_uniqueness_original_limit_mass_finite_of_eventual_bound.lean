-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_limit_mass_finite_of_eventual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:09:30.495421+00:00
-- url     : https://prove2.me/submissions/157924a5-b1d2-497b-9a33-78e275303c38

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A genuine limit of eventual uniformly bounded original masses remains
finite; this supplies the weighted X.ν image finiteness needed by P2-B. -/
theorem solution
    {ι : Type*} (l : Filter ι) [NeBot l]
    (μi : ι → Measure ℝ) (η : Measure ℝ) (C : ℝ≥0∞)
    (hC : C < ⊤)
    (hmass : ∀ᶠ i in l, (μi i) Set.univ ≤ C)
    (hlim : Tendsto (fun i => (μi i) Set.univ) l (nhds (η Set.univ))) :
    η Set.univ < ⊤ := by
  exact lt_of_le_of_lt (le_of_tendsto hlim hmass) hC
