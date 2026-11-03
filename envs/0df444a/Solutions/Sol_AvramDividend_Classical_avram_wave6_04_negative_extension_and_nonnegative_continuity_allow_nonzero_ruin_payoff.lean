-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_negative_extension_and_nonnegative_continuity_allow_nonzero_ruin_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:05:49.201037+00:00
-- url     : https://prove2.me/submissions/0579cfd6-fccf-4019-a132-ef58a1199674

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual source endpoint assumptions do not imply w(0)=0.
A payoff can be continuous on the nonnegative state half-line, vanish
strictly below ruin and still pay one upon exact landing at zero. -/
theorem solution :
    ∃ w : ℝ → ℝ,
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      w 0 = 1 := by
  refine ⟨(fun x : ℝ => if x < 0 then (0 : ℝ) else 1), ?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ici 0) :=
      continuousOn_const
    apply hc.congr
    intro x hx
    have hx0 : 0 ≤ x := hx
    simp [not_lt.mpr hx0]
  · intro y hy
    simp [hy]
  · norm_num
