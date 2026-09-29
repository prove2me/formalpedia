-- Prove2me | solution 2 for Erdos77.logarithmic_growth_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:28:24.100989+00:00
-- url     : https://prove2.me/submissions/b25a76a9-96ef-470f-9a63-bc03adc4d797
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
  refine ⟨?_, Erdos77.normalized_log_ramsey_tendsto⟩
  refine ⟨1, ?_⟩
  intro k hk
  have hkpos : 0 < k := by omega
  have hR : 1 ≤ Erdos77.diagonalRamsey k :=
    Erdos77.diagonalRamsey_ge_one k hkpos
  exact_mod_cast hR
