-- Prove2me | solution 1 for FongoSync.not_live_of_unknown_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:34.78943+00:00
-- url     : https://prove2.me/submissions/4e97dd30-9bbf-411e-90c6-85ac28779fb9

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (inp : Inputs) (g o : Gid) (f : Field)
    (hf : f ∈ sc.fields) (hkind : f.kind = .owner) (e : Entry Value)
    (he : register sc inp g f.name = some e) (hv : e.value = .ref o) (ho : o ∉ inp.gids) :
    ¬ Live sc inp g := by
  rintro ⟨k, hk⟩
  induction k with
  | zero => exact hk
  | succ k ih =>
    rcases hk with hk | ⟨_, _, hall⟩
    · exact ih hk
    · have := hall f hf hkind
      rw [he] at this
      simp only [ownerAllows, hv, namesLive] at this
      exact ho this.1
end FongoSync
