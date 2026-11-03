-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_negative_jump_generator_distinguishes_ruin_overshoot_from_zero_landing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:54:52.426736+00:00
-- url     : https://prove2.me/submissions/638e8838-de28-4e73-86a2-f6c73cfa1b5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict ruin overshoot uses the negative zero extension; exact
landing at zero retains w(0), with the source's exact (-1,1) small-mark
compensation. Continuity on the nonnegative half-line does not erase w(0). -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 < y)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0) :
    (∀ z : ℝ, z < -y →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        -w y - deriv w y * z * (Ioo (-1 : ℝ) 1).indicator 1 z) ∧
    SpectrallyNegativeLevy.generatorIntegrand w y (-y) =
      w 0 - w y - deriv w y * (-y) *
        (Ioo (-1 : ℝ) 1).indicator 1 (-y) := by
  constructor
  · intro z hz
    have hlt : y + z < 0 := by linarith
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hw_neg (y + z) hlt]
    ring
  · unfold SpectrallyNegativeLevy.generatorIntegrand
    simp
