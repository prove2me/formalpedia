-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_support_separated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:52.813989+00:00
-- url     : https://prove2.me/submissions/1c9fe4db-fbc6-48ed-9caa-de6ffd2db230

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology AvramDividend.Classical

/-- Compact negative test support lies in one finite-intensity band. -/
theorem solution
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ Function.support g ⊆ Iic (-ε) := by
  obtain ⟨ε, hε, hvan⟩ :=
    avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
      g hg hc hneg
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hxneg : x < 0 := hneg (subset_closure hx)
  have hnot : ¬ |x| < ε := by
    intro h
    exact hx (hvan x h)
  have habs : |x| = -x := abs_of_neg hxneg
  change x ≤ -ε
  linarith [le_of_not_gt hnot]
