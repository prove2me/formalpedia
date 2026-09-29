-- Prove2me | solution 1 for Erdos77.gnnw_diagonal_rate_37993
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:46:36.801511+00:00
-- url     : https://prove2.me/submissions/83057911-df97-4818-8721-43a8bd58529f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_diagonal_rate_exact
import Theorems.Thm_Erdos77_gnnw_optimized_base_lt_37993
import Definitions.Def_Erdos77_diagonal_ramsey
import Mathlib
open Filter Topology

theorem solution (eps : Real) (heps : 0 < eps) :
    Filter.Eventually
      (fun k : Nat =>
        (Erdos77.diagonalRamsey k : Real) <=
          (3.7993 : Real) ^ ((1 + eps) * (k : Real)))
      Filter.atTop := by
  have hbase :
      4 * Real.exp (- (0.14 : Real) / Real.exp 1) <= (3.7993 : Real) :=
    le_of_lt Erdos77.gnnw_optimized_base_lt_37993
  filter_upwards [Erdos77.gnnw_diagonal_rate_exact eps heps] with k hk
  exact hk.trans (Real.rpow_le_rpow (by positivity) hbase (by positivity))
