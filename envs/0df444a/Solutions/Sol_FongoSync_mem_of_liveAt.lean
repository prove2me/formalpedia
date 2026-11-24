-- Prove2me | solution 1 for FongoSync.mem_of_liveAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:49.413535+00:00
-- url     : https://prove2.me/submissions/c3beea0d-57af-44df-a3a6-b029dfc2ec37

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {k : Nat} {g : Gid} (h : liveAt sc inp k g) : g ∈ inp.gids := by
  induction k with
  | zero => exact h.elim
  | succ k ih =>
    rcases h with h | ⟨hm, _⟩
    · exact ih h
    · exact hm
end FongoSync
