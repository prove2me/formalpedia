-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_frozen_nonpositive_jump_cap_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:56:22.809735+00:00
-- url     : https://prove2.me/submissions/7a89484d-8310-4b47-a3b2-6ba036bff791

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_source_cap_splice_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped ENNReal

/-- A nonpositive original source jump preserves the finite-cap domain
of the cap-spliced C1 candidate, even if the jump causes ruin. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hd : d ≤ 0) :
    V (z + d) - V z = w (z + d) - w z := by
  have hzd : C = ⊤ ∨ z + d ≤ C.toReal := by
    rcases hz with htop | hzfin
    · exact Or.inl htop
    · exact Or.inr (by linarith)
  exact avram_p3_bv_frozen_source_cap_splice_step
    C w V hVtop hVfinite z d hz hzd
