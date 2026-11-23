-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_lw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:00.317119+00:00
-- url     : https://prove2.me/submissions/ab0a4076-1a1a-4f88-997f-e1726ef4ccdc

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution : ∀ (x y : Finset (Fin hrd.nStates)) (s : Fin hrd.nStates),
    hrd.lStepOf hrd_shape x y s ((hrd.lStepOf hrd_shape x y s)^[2] ∅)
      = (hrd.lStepOf hrd_shape x y s)^[2] ∅ := by
  decide
end Comp.HideOrRunData
