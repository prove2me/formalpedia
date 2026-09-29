-- Prove2me | solution 1 for CirclePackingConstants.r_n_sixteen_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:27:52.60934+00:00
-- url     : https://prove2.me/submissions/7e88144f-320c-48aa-a269-525ceca6c3be

import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : (1:ℝ)/8 ≤ r_n 16 := by
  have hbdd : BddAbove {r : ℝ | Packable 16 r} := ⟨1/2, fun r hr => hr.2.1⟩
  refine le_csSup hbdd ?_
  refine ⟨by norm_num, by norm_num,
    fun i => ((((2 * (i.val / 4) + 1 : ℕ) : ℝ)) / 8, (((2 * (i.val % 4) + 1 : ℕ) : ℝ)) / 8), ?_, ?_⟩
  · intro i
    fin_cases i <;> · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num

#print axioms solution
