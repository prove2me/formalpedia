-- Prove2me | solution 1 for BKAR.Forest.mem_activeEdges_of_not_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:33.963896+00:00
-- url     : https://prove2.me/submissions/8beb1482-bbff-4ea1-b28c-a570d4ec7ed9

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∈ F.activeEdges :=
  (F.mem_activeEdges_iff).mpr he
end BKAR.Forest
