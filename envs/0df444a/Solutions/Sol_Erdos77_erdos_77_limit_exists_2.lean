-- Prove2me | solution 2 for Erdos77.erdos_77_limit_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:20:51.87198+00:00
-- url     : https://prove2.me/submissions/d164fcd3-f6f4-4743-bc87-1bdf2f99d285
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_logarithmic_growth_limit
open Filter Topology

theorem solution :
    Exists fun L : Real =>
      Filter.Tendsto (fun k : Nat => (Erdos77.diagonalRamsey k : Real) ^ (1 / (k : Real)))
        atTop (nhds L) := by
  rcases Erdos77.logarithmic_growth_limit with ⟨⟨N, hpos⟩, l, hlog⟩
  refine ⟨Real.exp l, ?_⟩
  have hexp :
      Filter.Tendsto
        (fun k : Nat => Real.exp (Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real)))
        atTop (nhds (Real.exp l)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have heq :
      (fun k : Nat => (Erdos77.diagonalRamsey k : Real) ^ (1 / (k : Real))) =ᶠ[atTop]
        (fun k : Nat => Real.exp (Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real))) := by
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with k hk
    have hN : N ≤ k := le_trans (le_max_left N 1) hk
    have hk1 : 1 ≤ k := le_trans (le_max_right N 1) hk
    have hx : 0 < (Erdos77.diagonalRamsey k : Real) := hpos k hN
    have hk_nat : 0 < k := by omega
    have hk_real : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk_nat)
    rw [Real.rpow_def_of_pos hx]
    congr 1
    field_simp [hk_real]
  exact hexp.congr' heq.symm
