-- Prove2me | solution 1 for FongoSync.liveAt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:31.609865+00:00
-- url     : https://prove2.me/submissions/c72d2be1-46e9-4e8f-87f8-58dfa309e4a7

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (k : Nat) (g : Gid) :
    liveAt sc inp (k + 1) g ↔ liveAt sc inp k g ∨ rule sc inp (liveAt sc inp k) g := Iff.rfl
end FongoSync
