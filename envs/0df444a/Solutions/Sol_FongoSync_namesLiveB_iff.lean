-- Prove2me | solution 1 for FongoSync.namesLiveB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:01:42.885083+00:00
-- url     : https://prove2.me/submissions/b4c857ca-e3ff-4fc6-ae01-0ab24f812de2

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {live : Gid → Bool} {p : Gid → Prop} (h : ∀ m, live m = true ↔ p m)
    (o : Gid) : namesLiveB inp live o = true ↔ namesLive inp p o := by
  simp [namesLiveB, namesLive, h]
end FongoSync
