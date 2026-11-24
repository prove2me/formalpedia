-- Prove2me | solution 1 for FongoSync.deletedB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:56.659585+00:00
-- url     : https://prove2.me/submissions/aeb54e12-5a36-47d6-ac69-fb26c4912706

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (g : Gid) : deletedB sc inp g = true ↔ deleted sc inp g := by
  unfold deletedB deleted
  cases register sc inp g DELETED <;> simp
end FongoSync
