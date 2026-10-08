-- Prove2me | solution 1 for CirclePackingConstants.c_n_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:43:47.453009+00:00
-- url     : https://prove2.me/submissions/6806bd68-5ce6-4f6b-9c60-346918ec0b8f

import Theorems.Thm_CirclePackingConstants_r_n_sixteen_lower
import Theorems.Thm_CirclePackingConstants_r_n_sixteen_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : c_n 16 = Real.pi / 4 := by
  have h : r_n 16 = (1:ℝ)/8 :=
    le_antisymm r_n_sixteen_upper r_n_sixteen_lower
  unfold c_n
  rw [h]
  ring

#print axioms solution
