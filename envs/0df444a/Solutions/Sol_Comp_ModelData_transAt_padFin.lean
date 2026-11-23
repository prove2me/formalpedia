-- Prove2me | solution 1 for Comp.ModelData.transAt_padFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:10:29.648734+00:00
-- url     : https://prove2.me/submissions/f04fd27e-63c9-47bb-9b19-e1aa5220f57c

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_transAt_pad

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.transAt s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.transAt s a1 a2 :=
  d.transAt_pad s a1 a2
end ModelData
end Comp
