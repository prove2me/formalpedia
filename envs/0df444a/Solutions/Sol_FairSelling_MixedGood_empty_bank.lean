-- Prove2me | solution 1 for FairSelling.MixedGood.empty_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:06.022117+00:00
-- url     : https://prove2.me/submissions/ef078da3-4deb-4e82-b21a-458459b75e79

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution : (PhaseTPS.emptyPStage (Fin 3) 2).bank = 0 := rfl
end FairSelling.MixedGood
