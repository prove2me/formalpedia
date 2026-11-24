-- Prove2me | solution 1 for FongoSync.ownerAllowsB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:01.343452+00:00
-- url     : https://prove2.me/submissions/cdf7f54e-df5c-462d-a347-9e75abbfef2f

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_namesLiveB_iff

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {live : Gid → Bool} {p : Gid → Prop} (h : ∀ m, live m = true ↔ p m)
    (v : Option (Entry Value)) : ownerAllowsB inp live v = true ↔ ownerAllows inp p v := by
  cases v with
  | none => simp [ownerAllowsB, ownerAllows]
  | some e =>
    simp only [ownerAllowsB, ownerAllows]
    cases e.value <;> simp [namesLiveB_iff inp h]
end FongoSync
