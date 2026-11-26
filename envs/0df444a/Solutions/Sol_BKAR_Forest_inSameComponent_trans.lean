-- Prove2me | solution 1 for BKAR.Forest.inSameComponent_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:44.994801+00:00
-- url     : https://prove2.me/submissions/3e09ead0-2042-4dfb-a4a1-f413e3066b5d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_trans

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {i j k : V} (hij : F.inSameComponent i j)
    (hjk : F.inSameComponent j k) :
    F.inSameComponent i k :=
  F.acyclic.inSameComponent_trans hij hjk
end BKAR.Forest
