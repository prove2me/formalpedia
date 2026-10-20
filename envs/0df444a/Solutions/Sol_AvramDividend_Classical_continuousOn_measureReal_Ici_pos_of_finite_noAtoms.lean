-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_measureReal_Ici_pos_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:51:35.157583+00:00
-- url     : https://prove2.me/submissions/82741463-dd6b-4557-ba34-aa7910bc8e5a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_pos_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Atomless positive-height locally finite upper tails are continuous. -/
theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) := by
  exact AvramDividend.Classical.continuousOn_measureReal_Ici_of_pos_finite_noAtoms μ hfin
