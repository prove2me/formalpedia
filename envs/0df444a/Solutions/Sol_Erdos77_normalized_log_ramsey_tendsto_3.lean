-- Prove2me | solution 3 for Erdos77.normalized_log_ramsey_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T23:00:08.719259+00:00
-- url     : https://prove2.me/submissions/a6006a0a-ea1b-44ff-9f45-39c310895e4b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_erdos_77_limit_exists
import Theorems.Thm_Erdos77_diagonalRamsey_ge_one
import Theorems.Thm_Erdos77_rpow_tendsto_implies_log_div_tendsto
open Filter Topology

theorem solution :
    Exists fun l : Real =>
      Filter.Tendsto
        (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real) / (k : Real))
        atTop (nhds l) := by
  rcases Erdos77.erdos_77_limit_exists with ⟨L, hL⟩
  have hbase : ∀ k : Nat, 0 < k → 1 ≤ (Erdos77.diagonalRamsey k : Real) := by
    intro k hk
    have h := Erdos77.diagonalRamsey_ge_one k hk
    exact_mod_cast h
  have ha : ∀ᶠ k : Nat in atTop, 1 ≤ (Erdos77.diagonalRamsey k : Real) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hbase k (by omega)
  have hpow : ∀ᶠ k : Nat in atTop,
      1 ≤ (Erdos77.diagonalRamsey k : Real) ^ (1 / (k : Real)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact Real.one_le_rpow (hbase k (by omega)) (by positivity)
  have hLlower : 1 ≤ L :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hL hpow
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLlower
  exact Erdos77.rpow_tendsto_implies_log_div_tendsto
    (fun k : Nat => (Erdos77.diagonalRamsey k : Real)) L ha hL hLpos
