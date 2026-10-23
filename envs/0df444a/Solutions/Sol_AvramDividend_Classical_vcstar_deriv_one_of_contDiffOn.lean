-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:36:43.185827+00:00
-- url     : https://prove2.me/submissions/f52437f5-dd9f-4fd4-8ed8-09f41eb5b904

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hca : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hDiff : DifferentiableAt ℝ
      (barrierValue W (cstar W).toReal) (cstar W).toReal := by
    change DifferentiableAt ℝ (vcstar W) (cstar W).toReal
    have hDiffOn : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) :=
      hsmooth.differentiableOn (by norm_num)
    have hmem : (cstar W).toReal ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr hca
    exact (hDiffOn _ hmem).differentiableAt (isOpen_Ioi.mem_nhds hmem)
  change deriv (barrierValue W (cstar W).toReal) (cstar W).toReal = 1
  exact barrierValue_deriv_one_of_differentiableAt
    W (cstar W).toReal (le_of_lt hca) hDiff
