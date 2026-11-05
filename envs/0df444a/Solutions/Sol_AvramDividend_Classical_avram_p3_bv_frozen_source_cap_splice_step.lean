-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_frozen_source_cap_splice_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:48:32.857301+00:00
-- url     : https://prove2.me/submissions/31e422b7-2959-43af-8e33-e1dd3d414fa2

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-- A frozen source step entirely below the finite cap has the same
increment for the cap-spliced candidate as for the original candidate.
The infinite-cap case is included without using `toReal` there. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hzd : C = ⊤ ∨ z + d ≤ C.toReal) :
    V (z + d) - V z = w (z + d) - w z := by
  by_cases htop : C = ⊤
  · rw [hVtop htop (z + d), hVtop htop z]
  · have hzfin : z ≤ C.toReal := hz.resolve_left htop
    have hzdfin : z + d ≤ C.toReal := hzd.resolve_left htop
    rw [hVfinite htop (z + d), hVfinite htop z]
    simp only [if_pos hzdfin, if_pos hzfin]
