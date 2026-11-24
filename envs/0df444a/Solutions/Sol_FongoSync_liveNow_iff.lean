-- Prove2me | solution 1 for FongoSync.liveNow_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:14.221566+00:00
-- url     : https://prove2.me/submissions/f6b6a4b3-1acf-414b-a1ae-d71808542eb7

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_live_iff_liveAt_length
import Theorems.Thm_FongoSync_liveB_iff

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (g : Gid) : liveNow sc inp g = true ↔ Live sc inp g := by
  rw [live_iff_liveAt_length, liveNow, liveB_iff]
end FongoSync
