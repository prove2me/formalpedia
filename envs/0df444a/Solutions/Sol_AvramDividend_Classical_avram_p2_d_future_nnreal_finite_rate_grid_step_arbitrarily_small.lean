-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:54:59.741668+00:00
-- url     : https://prove2.me/submissions/b40c0dad-5a08-496a-87f7-dc712a215e16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The finite slope contribution of a rational grid cell tends to zero as
the integer denominator grows; this is a constructive epsilon witness. -/
theorem solution
    (c ε : ℝ≥0) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ c / (d : ℝ≥0) < ε := by
  obtain ⟨d, hd⟩ := exists_nat_gt (c / ε)
  have hdpos : (0 : ℝ≥0) < (d : ℝ≥0) :=
    lt_of_le_of_lt (bot_le : (0 : ℝ≥0) ≤ c / ε) hd
  have hdc : c < (d : ℝ≥0) * ε :=
    (div_lt_iff₀ hε).mp hd
  refine ⟨d, ?_, ?_⟩
  · exact_mod_cast hdpos
  · apply (div_lt_iff₀ hdpos).2
    simpa [mul_comm] using hdc
