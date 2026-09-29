-- Prove2me | solution 1 for CirclePackingConstants.r_n_twenty_five_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:30:59.430443+00:00
-- url     : https://prove2.me/submissions/b8e3692d-6f09-4abc-8721-1cdd906560e9

import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : (1:ℝ)/10 ≤ r_n 25 := by
  have hbdd : BddAbove {r : ℝ | Packable 25 r} := ⟨1/2, fun r hr => hr.2.1⟩
  refine le_csSup hbdd ?_
  refine ⟨by norm_num, by norm_num,
    fun i => ((((2 * (i.val / 5) + 1 : ℕ) : ℝ)) / 10, (((2 * (i.val % 5) + 1 : ℕ) : ℝ)) / 10), ?_, ?_⟩
  · intro i
    fin_cases i <;> · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num

#print axioms solution
