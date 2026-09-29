-- Prove2me | solution 2 for Erdos77.normalized_log_ramsey_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:54:38.359978+00:00
-- url     : https://prove2.me/submissions/f8d9aa37-087a-4485-af3f-3efeb9048264
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_erdos_77_limit_exists
import Theorems.Thm_Erdos77_diagonalRamsey_ge_one
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
  have hpow : ∀ᶠ k : Nat in atTop,
      1 ≤ (Erdos77.diagonalRamsey k : Real) ^ (1 / (k : Real)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact Real.one_le_rpow (hbase k (by omega)) (by positivity)
  have hLlower : 1 ≤ L :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hL hpow
  have hlog : Filter.Tendsto
      (fun k : Nat => Real.log ((Erdos77.diagonalRamsey k : Real) ^ (1 / (k : Real))))
      atTop (nhds (Real.log L)) :=
    (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hLlower))).tendsto.comp hL
  refine ⟨Real.log L, ?_⟩
  apply hlog.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkpos : 0 < k := by omega
  have hRpos : 0 < (Erdos77.diagonalRamsey k : Real) :=
    lt_of_lt_of_le zero_lt_one (hbase k hkpos)
  rw [Real.log_rpow hRpos]
  have hkne : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  field_simp
