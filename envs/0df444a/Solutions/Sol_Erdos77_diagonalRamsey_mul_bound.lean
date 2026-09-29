-- Prove2me | solution 1 for Erdos77.diagonalRamsey_mul_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:43:59.276993+00:00
-- url     : https://prove2.me/submissions/141f33ca-66ed-44d0-a670-be7c6b48c1f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_diagonalRamsey_product_graph_property

theorem solution (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    Erdos77.diagonalRamsey (m + n) ≤ Erdos77.diagonalRamsey m * Erdos77.diagonalRamsey n := by
  unfold Erdos77.diagonalRamsey
  apply Nat.sInf_le
  exact Erdos77.diagonalRamsey_product_graph_property m n hm hn
