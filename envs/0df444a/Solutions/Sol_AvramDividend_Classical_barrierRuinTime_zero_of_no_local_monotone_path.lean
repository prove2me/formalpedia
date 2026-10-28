-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_of_no_local_monotone_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:38:26.277918+00:00
-- url     : https://prove2.me/submissions/607064a6-9436-4250-a0be-a9f7a17724db

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Mathlib.Order.Interval.Set.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every neighbourhood of the origin having a nonmonotone path segment
forces immediate zero-barrier reflected ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNoMono : ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    barrierRuinTime X 0 ω = 0 := by
  apply barrierRuinTime_zero_of_near_zero_path_decrease X ω
  intro ε hε
  have hhalfpos : 0 < ε / 2 := half_pos hε
  have hhalflt : ε / 2 < ε := half_lt_self hε
  have hnot := hNoMono (ε / 2) hhalfpos
  have hfailure :
      ∃ s : ℝ≥0, s ∈ Icc 0 (ε / 2) ∧
        ∃ t : ℝ≥0, t ∈ Icc 0 (ε / 2) ∧
          s ≤ t ∧ ¬ X.X s ω ≤ X.X t ω := by
    classical
    by_contra h
    apply hnot
    intro s hs t ht hst
    by_contra hn
    exact h ⟨s, hs, t, ht, hst, hn⟩
  obtain ⟨s, hs, t, ht, hst, hdrop⟩ := hfailure
  exact ⟨s, t, hst, lt_of_le_of_lt ht.2 hhalflt, lt_of_not_ge hdrop⟩
