-- Prove2me | solution 1 for FongoSync.Laws.observe_ignores_unencodable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:52.639078+00:00
-- url     : https://prove2.me/submissions/93aa4b2c-7222-4c7f-9816-cea64786b1d3

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Clock_observe_ignores


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (c : Clock) (remote : Hlc) (h : ¬ remote.encodable) :
    c.observe remote = c :=
  c.observe_ignores remote h
end FongoSync.Laws
