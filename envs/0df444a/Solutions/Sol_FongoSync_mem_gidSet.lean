-- Prove2me | solution 1 for FongoSync.mem_gidSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:07.603549+00:00
-- url     : https://prove2.me/submissions/b9a23ea1-364a-4c61-8cf5-a37e0cc0493f

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
import Theorems.Thm_FongoSync_mem_insertGid

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {x : Gid} {l : List Gid} : x ∈ gidSet l ↔ x ∈ l := by
  induction l with
  | nil => simp [gidSet]
  | cons h t ih =>
    simp only [gidSet, List.foldr_cons] at *
    rw [mem_insertGid, ih, List.mem_cons]
end FongoSync
