-- Prove2me | solution 1 for FongoSync.Laws.view_from_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:00.832668+00:00
-- url     : https://prove2.me/submissions/33b415c0-b5dc-4038-ac42-c0fa6545a5ef

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_view_from_inputs


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (h : inputs sc cs₁ = inputs sc cs₂) : view sc cs₁ = view sc cs₂ :=
  FongoSync.view_from_inputs sc h
end FongoSync.Laws
