-- Prove2me | solution 1 for CirclePackingConstants.r_n_thirty_six_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:34:45.769439+00:00
-- url     : https://prove2.me/submissions/25cceae1-bc38-4fd4-8272-c7707eb33754

import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : (1:ℝ)/12 ≤ r_n 36 := by
  have hbdd : BddAbove {r : ℝ | Packable 36 r} := ⟨1/2, fun r hr => hr.2.1⟩
  refine le_csSup hbdd ?_
  refine ⟨by norm_num, by norm_num,
    fun i => ((((2 * (i.val / 6) + 1 : ℕ) : ℝ)) / 12, (((2 * (i.val % 6) + 1 : ℕ) : ℝ)) / 12), ?_, ?_⟩
  · intro i
    fin_cases i <;> · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num

#print axioms solution
