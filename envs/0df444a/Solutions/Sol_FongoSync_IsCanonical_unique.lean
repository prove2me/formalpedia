-- Prove2me | solution 1 for FongoSync.IsCanonical.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:03.544462+00:00
-- url     : https://prove2.me/submissions/375e1fee-43a7-4290-ad28-25f03a4e6bbf

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace IsCanonical
theorem _root_.solution {E : List Edge} {g r r' : Gid} (h : IsCanonical E g r)
    (h' : IsCanonical E g r') : r = r' :=
  Nat.le_antisymm (h.2 r' h'.1) (h'.2 r h.1)
end IsCanonical
end FongoSync
