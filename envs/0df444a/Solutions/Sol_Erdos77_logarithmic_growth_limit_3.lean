-- Prove2me | solution 3 for Erdos77.logarithmic_growth_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T22:25:44.001395+00:00
-- url     : https://prove2.me/submissions/2c5d70e9-5ff0-4577-ba48-1d4d10724b37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_normalized_log_ramsey_tendsto
import Theorems.Thm_Erdos77_diagonalRamsey_ge_one
open Filter Topology

theorem solution :
    And (Exists fun N : Nat => forall k : Nat, N <= k ->
      0 < (Erdos77.diagonalRamsey k : Real))
    (Exists fun l : Real =>
      Filter.Tendsto
        (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l)) := by
  refine ⟨⟨1, ?_⟩, Erdos77.normalized_log_ramsey_tendsto⟩
  intro k hk
  have hkpos : 0 < k := by omega
  have hR : 1 ≤ Erdos77.diagonalRamsey k :=
    Erdos77.diagonalRamsey_ge_one k hkpos
  have hRpos : 0 < Erdos77.diagonalRamsey k := by omega
  exact_mod_cast hRpos
