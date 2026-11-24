-- Prove2me | solution 1 for FongoSync.label_eq_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:29.732339+00:00
-- url     : https://prove2.me/submissions/fd136b5d-b780-4aa6-8f09-bd9fa404dc4d

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv
namespace FongoSync
theorem _root_.solution {g h : Gid} (c : Connected P g h) : L g = L h :=
  Nat.le_antisymm ((inv g).2 _ (.trans c (inv h).1)) ((inv h).2 _ (.trans (.symm c) (inv g).1))
end FongoSync
