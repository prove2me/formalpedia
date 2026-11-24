-- Prove2me | solution 1 for FongoSync.sorted_gidSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:33.272198+00:00
-- url     : https://prove2.me/submissions/6792006a-ba86-4c04-b747-479a4761b29e

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
import Theorems.Thm_FongoSync_sorted_insertGid

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (l : List Gid) : (gidSet l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [gidSet]
  | cons h t ih => exact sorted_insertGid ih
end FongoSync
