-- Prove2me | solution 2 for Erdos77.erdos_szekeres_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:21:32.536981+00:00
-- url     : https://prove2.me/submissions/2981bb92-00c0-4115-b6ec-5f9a1f84ef59

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
