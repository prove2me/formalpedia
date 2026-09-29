-- Prove2me | solution 1 for CirclePackingConstants.c_n_thirty_six
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:46:17.762016+00:00
-- url     : https://prove2.me/submissions/a01a7e65-09d2-4bdb-9069-de01bde43648
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CirclePackingConstants_r_n_thirty_six_lower
import Theorems.Thm_CirclePackingConstants_r_n_thirty_six_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : c_n 36 = Real.pi / 4 := by
  have h : r_n 36 = (1:ℝ)/12 :=
    le_antisymm r_n_thirty_six_upper r_n_thirty_six_lower
  unfold c_n
  rw [h]
  ring

#print axioms solution
