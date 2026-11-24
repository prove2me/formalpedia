-- Prove2me | solution 1 for FongoSync.liveAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:28.332558+00:00
-- url     : https://prove2.me/submissions/68f18b25-29ab-461a-b05d-39c1f7abacdc

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveAt_succ_of

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {k j : Nat} (hkj : k ≤ j) {g : Gid} (h : liveAt sc inp k g) :
    liveAt sc inp j g := by
  induction hkj with
  | refl => exact h
  | step _ ih => exact liveAt_succ_of sc inp ih
end FongoSync
