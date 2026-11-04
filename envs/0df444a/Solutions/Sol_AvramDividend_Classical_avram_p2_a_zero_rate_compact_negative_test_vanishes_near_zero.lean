-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:38:16.99601+00:00
-- url     : https://prove2.me/submissions/110d115e-2cda-410f-8776-3c613001fd3d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_separation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical

/-- Continuous tests with compact strictly negative support vanish in a full neighbourhood of zero. -/
theorem solution
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, |z| < ρ → g z = 0 := by
  obtain ⟨ρ, hρ, hgap⟩ :=
    avram_p2_j_ui_compact_negative_support_separation
      (tsupport g) hc hneg
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  have hnot : z ∉ tsupport g := by
    intro hs
    exact (not_le_of_gt (abs_lt.mp hz).1) (hgap z hs)
  exact image_eq_zero_of_notMem_tsupport hnot
