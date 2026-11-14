-- Prove2me | solution 1 for BCFGJPSSV26.FL.lmp_of_score
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:52.327644+00:00
-- url     : https://prove2.me/submissions/6c6ba912-c243-4471-9b1e-151ed956905d

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_Select
import all Definitions.Def_BCFGJPSSV26_FL_Select

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-- **The LMP guarantee from the objective**: `cost S + λ f |S| ≤ λ OPT_f` is
`cost S ≤ λ (OPT_f - f |S|)`. -/
theorem lmp_of_score {S : List ℕ} (hS : I.IsCenterList S) {f : ℚ}
    (h : (score (toRaw I) f S : ℝ) ≤ (lmpC : ℝ) * I.optFL f) :
    I.cost (I.centers S) ≤ 1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * S.length) := by
  rw [score_cast hS.1 hS.2.2, lmpC_cast] at h
  linarith

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.lmp_of_score := @BCFGJPSSV26.FL.lmp_of_score
