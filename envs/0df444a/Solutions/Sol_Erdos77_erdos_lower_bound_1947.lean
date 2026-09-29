-- Prove2me | solution 1 for Erdos77.erdos_lower_bound_1947
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:01:38.727485+00:00
-- url     : https://prove2.me/submissions/e03f02ae-39cd-4dbc-a89f-dd0645285e83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_erdos_1947_bad_graph_exists
import Theorems.Thm_Erdos77_erdos_1947_ramsey_finiteness
import Theorems.Thm_Erdos77_erdos_1947_finite_and_bad_graph_bound
open Filter Topology

theorem solution (k : Nat) (hk : 3 <= k) :
    (2 : Real) ^ ((k : Real) / 2) < (Erdos77.diagonalRamsey k : Real) := by
  have hk1 : 1 <= k := Nat.le_trans (by decide) hk
  exact Erdos77.erdos_1947_finite_and_bad_graph_bound k hk
    (Erdos77.erdos_1947_ramsey_finiteness k hk1)
    (Erdos77.erdos_1947_bad_graph_exists k hk)