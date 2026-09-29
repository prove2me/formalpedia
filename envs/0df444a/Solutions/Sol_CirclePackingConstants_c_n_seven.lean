-- Prove2me | solution 1 for CirclePackingConstants.c_n_seven
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:58:29.172744+00:00
-- url     : https://prove2.me/submissions/b8bde9f1-37a3-4a7f-9162-9d7693a855ce

import Theorems.Thm_CirclePackingConstants_r_n_seven_lower
import Theorems.Thm_CirclePackingConstants_r_n_seven_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution :
    c_n 7 = 7 * Real.pi *
      (((4 - 2 * Real.sqrt 3) / (2 * (1 + (4 - 2 * Real.sqrt 3))))) ^ 2 := by
  have h : r_n 7 = (4 - 2 * Real.sqrt 3) / (2 * (1 + (4 - 2 * Real.sqrt 3))) :=
    le_antisymm r_n_seven_upper r_n_seven_lower
  unfold c_n
  rw [h]
  norm_num

#print axioms solution
