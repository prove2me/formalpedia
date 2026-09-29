-- Prove2me | solution 1 for CirclePackingConstants.c_n_six
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:56:49.396041+00:00
-- url     : https://prove2.me/submissions/98d09cf0-e778-4358-b5f9-8580b2fee3f5

import Theorems.Thm_CirclePackingConstants_r_n_six_lower
import Theorems.Thm_CirclePackingConstants_r_n_six_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution :
    c_n 6 = 6 * Real.pi *
      (((Real.sqrt 13 / 6) / (2 * (1 + Real.sqrt 13 / 6)))) ^ 2 := by
  have h : r_n 6 = (Real.sqrt 13 / 6) / (2 * (1 + Real.sqrt 13 / 6)) :=
    le_antisymm r_n_six_upper r_n_six_lower
  unfold c_n
  rw [h]
  norm_num

#print axioms solution
