-- Prove2me | solution 1 for Erdos77.erdos_szekeres_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T09:53:35.157076+00:00
-- url     : https://prove2.me/submissions/8060864b-a5dc-462c-8ed4-2b738f1ddf01

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_erdos_szekeres_asymmetric_graph_bound
open Filter Topology

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    Erdos77.diagonalRamsey k ≤ Nat.choose (2 * k - 2) (k - 1) := by
  unfold Erdos77.diagonalRamsey
  apply Nat.sInf_le
  have hArg : 2 * k - 2 = k + k - 2 := by omega
  rw [hArg]
  exact erdos_szekeres_asymmetric_graph_bound k k hk hk
