-- Prove2me | solution 1 for FongoSync.label_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:12.348822+00:00
-- url     : https://prove2.me/submissions/0da022fa-b594-42aa-b7cc-9ea27198ede4

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv
namespace FongoSync
theorem _root_.solution (g : Gid) : L g ≤ g := (inv g).2 g (.refl g)
end FongoSync
