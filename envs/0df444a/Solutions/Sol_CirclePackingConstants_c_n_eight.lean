-- Prove2me | solution 1 for CirclePackingConstants.c_n_eight
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T03:00:08.595342+00:00
-- url     : https://prove2.me/submissions/90437c1e-1ddb-48d3-b8bd-8e52257e602f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CirclePackingConstants_r_n_eight_lower
import Theorems.Thm_CirclePackingConstants_r_n_eight_upper
import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open CirclePackingConstants

theorem _root_.solution :
    c_n 8 = 8 * Real.pi *
      (((Real.sqrt (2 - Real.sqrt 3)) /
        (2 * (1 + Real.sqrt (2 - Real.sqrt 3))))) ^ 2 := by
  have h : r_n 8 = (Real.sqrt (2 - Real.sqrt 3)) / (2 * (1 + Real.sqrt (2 - Real.sqrt 3))) :=
    le_antisymm r_n_eight_upper r_n_eight_lower
  unfold c_n
  rw [h]
  norm_num

#print axioms solution
