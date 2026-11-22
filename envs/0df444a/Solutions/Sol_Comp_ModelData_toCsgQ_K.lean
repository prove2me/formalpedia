-- Prove2me | solution 1 for Comp.ModelData.toCsgQ_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:38:44.456044+00:00
-- url     : https://prove2.me/submissions/01a20eb8-6324-4145-9f23-f1eb41dbf4ae

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) (s' : Fin d.nStates) :
    d.toCsgQ.K s a1 a2 s' = denseOf d.nStates (d.transAt s a1 a2).dist s' := rfl
end ModelData
end Comp
