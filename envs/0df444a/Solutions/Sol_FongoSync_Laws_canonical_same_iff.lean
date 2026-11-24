-- Prove2me | solution 1 for FongoSync.Laws.canonical_same_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:53.452261+00:00
-- url     : https://prove2.me/submissions/041c37f8-407d-4828-b29d-564409c1f089

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_canonical_eq_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (E : List Edge) (a b : Gid) :
    canonical E a = canonical E b ↔ Connected E a b :=
  canonical_eq_iff E a b
end FongoSync.Laws
