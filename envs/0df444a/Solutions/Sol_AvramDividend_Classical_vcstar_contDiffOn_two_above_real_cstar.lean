-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_contDiffOn_two_above_real_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:34:52.002497+00:00
-- url     : https://prove2.me/submissions/c4513e8c-88d9-4098-a240-4b95fffa9629

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_contDiffOn_above_real_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (cstar W).toReal) := by
  change ContDiffOn ℝ 2 (barrierValue W (cstar W).toReal) (Ioi (cstar W).toReal)
  exact barrierValue_contDiffOn_above_real_barrier
    W (cstar W).toReal ENNReal.toReal_nonneg
