-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_linear_gt_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:25:43.377749+00:00
-- url     : https://prove2.me/submissions/e2a46336-9d59-49a1-8e90-d62d25d91b86

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (z : ℝ) (hz : (cstar W).toReal < z) :
    vcstar W z =
      z - (cstar W).toReal +
        divE (W (cstar W).toReal) (scaleDeriv W (cstar W).toReal) := by
  have ha0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have hz0 : ¬ z < 0 := not_lt.mpr (le_trans ha0 hz.le)
  change barrierValue W (cstar W).toReal z =
    z - (cstar W).toReal +
      divE (W (cstar W).toReal) (scaleDeriv W (cstar W).toReal)
  simp [barrierValue, hz0, not_le.mpr hz]
