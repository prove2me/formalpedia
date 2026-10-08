-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_scaledW_le_cstar_of_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:19.09665+00:00
-- url     : https://prove2.me/submissions/21d9cc37-cfbd-4000-9d86-86f25cc4ad64

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (z : ℝ) (hz : z ≤ (cstar W).toReal) :
    vcstar W z = divE (W z) (scaleDeriv W (cstar W).toReal) := by
  by_cases hz0 : z < 0
  · have hWz : W z = 0 := hsupport z hz0
    simp [vcstar, barrierValue, hz0, divE, hWz]
  · have hznonneg : 0 ≤ z := le_of_not_gt hz0
    simp [vcstar, barrierValue, hz0, hz]
