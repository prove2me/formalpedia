-- Prove2me | solution 1 for FongoSync.live_of_unowned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:31.47947+00:00
-- url     : https://prove2.me/submissions/450a8eea-42e6-4b81-a65f-90e50084e8ad

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (inp : Inputs) (g : Gid)
    (hk : g ∈ inp.gids) (hd : ¬ deleted sc inp g)
    (ho : ∀ f ∈ sc.fields, f.kind = .owner → register sc inp g f.name = none) :
    Live sc inp g :=
  ⟨1, .inr ⟨hk, hd, fun f hf hkind => by rw [ho f hf hkind]; trivial⟩⟩
end FongoSync
