-- Prove2me | solution 1 for CirclePackingConstants.c_n_twenty_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:45:02.498494+00:00
-- url     : https://prove2.me/submissions/a41900a9-d1e0-4edc-8b3d-f2c2bb0422ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CirclePackingConstants_r_n_twenty_five_lower
import Theorems.Thm_CirclePackingConstants_r_n_twenty_five_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution : c_n 25 = Real.pi / 4 := by
  have h : r_n 25 = (1:ℝ)/10 :=
    le_antisymm r_n_twenty_five_upper r_n_twenty_five_lower
  unfold c_n
  rw [h]
  ring

#print axioms solution
