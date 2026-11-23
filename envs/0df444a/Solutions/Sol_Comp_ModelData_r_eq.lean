-- Prove2me | solution 1 for Comp.ModelData.r_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:46.577872+00:00
-- url     : https://prove2.me/submissions/615bb0a1-86a3-4609-b5e1-35432b2a0f15

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.r s a1 a2 = (d.stateAt s).rew + (d.transAt s a1 a2).rew := rfl
end ModelData
end Comp
