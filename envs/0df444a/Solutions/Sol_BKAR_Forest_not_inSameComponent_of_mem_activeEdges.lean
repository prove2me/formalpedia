-- Prove2me | solution 1 for BKAR.Forest.not_inSameComponent_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:09.265081+00:00
-- url     : https://prove2.me/submissions/dc61974c-a30c-4028-a8ba-80e4239b3e63

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    ¬ F.inSameComponent e.left e.right :=
  (F.mem_activeEdges_iff).mp he
end BKAR.Forest
