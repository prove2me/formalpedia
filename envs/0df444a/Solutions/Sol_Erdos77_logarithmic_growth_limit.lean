-- Prove2me | solution 1 for Erdos77.logarithmic_growth_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:49:22.293976+00:00
-- url     : https://prove2.me/submissions/41d12112-ff42-4670-8157-7dd4cdbb075a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_diagonalRamsey_log_subadditive
open Filter Topology

theorem solution :
    And (Exists fun N : Nat => forall k : Nat, N <= k ->
      0 < (Erdos77.diagonalRamsey k : Real))
    (Exists fun l : Real =>
      Filter.Tendsto
        (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l)) := by
  rcases Erdos77.diagonalRamsey_log_subadditive with ⟨hsub, hnonneg, hpos⟩
  refine ⟨hpos, ?_⟩
  have hbound : BddBelow (Set.range fun k : Nat =>
      Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact div_nonneg (hnonneg k) (Nat.cast_nonneg k)
  exact ⟨hsub.lim, hsub.tendsto_lim hbound⟩
