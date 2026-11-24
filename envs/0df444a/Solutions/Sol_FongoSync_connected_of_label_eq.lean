-- Prove2me | solution 1 for FongoSync.connected_of_label_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:34.286095+00:00
-- url     : https://prove2.me/submissions/eaaf8671-8e3d-44dd-a6c7-f0a9f8860ece

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv
namespace FongoSync
theorem _root_.solution {g h : Gid} (e : L g = L h) : Connected P g h :=
  .trans (inv g).1 (e ▸ .symm (inv h).1)
end FongoSync
