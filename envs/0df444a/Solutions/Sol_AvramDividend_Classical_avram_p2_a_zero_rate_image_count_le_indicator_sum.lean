-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_image_count_le_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:17:32.123454+00:00
-- url     : https://prove2.me/submissions/be6d1e3f-80c1-4ad5-b5eb-e5e8a730e12f

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_filter_image_card_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset AvramDividend.Classical
open scoped ENNReal BigOperators

/-- A marked image grid count is bounded by the ENNReal sum of indicators
of its original finite source cells, with no injectivity assumption. -/
theorem solution
    {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (p : β → Prop) [DecidablePred p] :
    (((s.image f).filter p).card : ℝ≥0∞) ≤
      ∑ a ∈ s, if p (f a) then (1 : ℝ≥0∞) else 0 := by
  calc
    (((s.image f).filter p).card : ℝ≥0∞) ≤
        ((s.filter (fun a => p (f a))).card : ℝ≥0∞) := by
      exact_mod_cast (avram_p2_a_zero_rate_filter_image_card_le s f p)
    _ = _ := by
      rw [Finset.card_filter]
      norm_cast
