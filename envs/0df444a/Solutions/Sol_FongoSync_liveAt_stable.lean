-- Prove2me | solution 1 for FongoSync.liveAt_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:09.480751+00:00
-- url     : https://prove2.me/submissions/c1714567-c5d0-46a4-b2b7-9e3ca8bf0d0d

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveAt_succ
import Theorems.Thm_FongoSync_rule_congr

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {k : Nat} (hs : ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g)
    (j : Nat) (g : Gid) : liveAt sc inp (k + j) g ↔ liveAt sc inp k g := by
  induction j generalizing g with
  | zero => exact Iff.rfl
  | succ j ih =>
    rw [← Nat.add_assoc, liveAt_succ, ih]
    constructor
    · rintro (h | h)
      · exact h
      · have hr : rule sc inp (liveAt sc inp k) g :=
          (rule_congr sc inp (fun m _ => ih m) g).mp h
        exact hs g hr.1 (.inr hr)
    · exact .inl
end FongoSync
