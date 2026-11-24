-- Prove2me | solution 1 for FongoSync.liveMembersR_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:39.08914+00:00
-- url     : https://prove2.me/submissions/838fe7e6-7660-481c-b3d1-a137f3bc6765

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveNow_iff

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (r : Gid) : liveMembersR sc inp r = liveMembers sc inp r := by
  unfold liveMembersR liveMembers
  congr
  funext m
  have := liveNow_iff sc inp m
  cases hb : liveNow sc inp m <;> by_cases hc : inp.canon m = r <;> simp_all
end FongoSync
