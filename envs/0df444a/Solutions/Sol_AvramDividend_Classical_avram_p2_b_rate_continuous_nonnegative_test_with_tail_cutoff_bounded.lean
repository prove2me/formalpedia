-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_continuous_nonnegative_test_with_tail_cutoff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:29:46.23094+00:00
-- url     : https://prove2.me/submissions/626e4485-7d5f-45ec-ba84-044f288a217e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (g : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hcont : ContinuousOn g (Ici 0))
    (hzero : ∀ z : ℝ, R < z → g z = 0) :
    Bornology.IsBounded (g '' Ici (0 : ℝ)) := by
  have hcontIcc : ContinuousOn g (Icc 0 R) :=
    hcont.mono (by
      intro z hz
      exact hz.1)
  have hcompact : IsCompact (g '' Icc (0 : ℝ) R) :=
    isCompact_Icc.image_of_continuousOn hcontIcc
  have hbig : IsCompact (insert (0 : ℝ) (g '' Icc (0 : ℝ) R)) :=
    hcompact.insert 0
  apply hbig.isBounded.subset
  rintro y ⟨z, hz, rfl⟩
  by_cases hzr : z ≤ R
  · exact (Set.mem_insert_iff).2 (Or.inr ⟨z, ⟨hz, hzr⟩, rfl⟩)
  · have hzzero : g z = 0 := hzero z (lt_of_not_ge hzr)
    exact (Set.mem_insert_iff).2 (Or.inl hzzero)
