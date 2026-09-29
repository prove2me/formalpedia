-- Prove2me | solution 1 for Erdos77.normalized_log_ramsey_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:39:15.691142+00:00
-- url     : https://prove2.me/submissions/9bdb8620-cfdc-4890-a417-9e4b6e371e34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_diagonalRamsey_log_subadditive
open Filter Topology

theorem solution :
    Exists fun l : Real =>
      Filter.Tendsto
        (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l) := by
  let u : Nat → Real := fun k => Real.log (Erdos77.diagonalRamsey k : Real)
  have hdata := Erdos77.diagonalRamsey_log_subadditive
  rcases hdata with ⟨hsub, hnonneg, hpos⟩
  have hbdd : BddBelow (Set.range fun n : Nat => u n / (n : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn, u]
    · have hn' : 0 < (n : Real) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hlog : 0 ≤ u n := by simpa [u] using hnonneg n
      exact div_nonneg hlog (le_of_lt hn')
  refine ⟨Subadditive.lim hsub, ?_⟩
  simpa [u] using hsub.tendsto_lim hbdd
