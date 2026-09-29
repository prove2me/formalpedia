-- Prove2me | solution 1 for Erdos77.gnnw_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T09:52:29.342986+00:00
-- url     : https://prove2.me/submissions/da56eae3-91cf-44da-9c9d-2da8252ef312
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_gnnw_diagonal_rate_37993
import Definitions.Def_Erdos77_diagonal_ramsey
import Mathlib
open Erdos77 Filter Topology

theorem solution (d : Real) (hd : 0 < d) :
    Filter.Eventually
      (fun k : Nat =>
        (diagonalRamsey k : Real) <=
          (3.8 : Real) ^ ((1 + d) * (k : Real)))
      Filter.atTop := by
  filter_upwards [Erdos77.gnnw_diagonal_rate_37993 d hd] with k hk
  exact hk.trans (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity))