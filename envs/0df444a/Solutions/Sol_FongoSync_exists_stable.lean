-- Prove2me | solution 1 for FongoSync.exists_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:23.825148+00:00
-- url     : https://prove2.me/submissions/bc2e1297-efaf-4608-9574-9903ce3905da

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveCount_le
import Theorems.Thm_FongoSync_liveCount_lt

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution : ∃ k ≤ inp.gids.length,
    ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g := by
  apply Classical.byContradiction
  intro hno
  have grow : ∀ k ≤ inp.gids.length + 1, k ≤ liveCount sc inp k := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk' : k ≤ inp.gids.length := by omega
      have := liveCount_lt sc inp (fun hs => hno ⟨k, hk', hs⟩)
      have := ih (by omega)
      omega
  have := grow (inp.gids.length + 1) (Nat.le_refl _)
  have := liveCount_le sc inp (inp.gids.length + 1)
  omega
end FongoSync
