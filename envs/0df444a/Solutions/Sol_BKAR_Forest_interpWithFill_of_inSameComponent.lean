-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_of_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:20.369514+00:00
-- url     : https://prove2.me/submissions/e76d97cb-a5af-4609-8ba6-8a6d03006d75

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = F.pathMin u (F.pathInF e.left e.right he) := by
  rw [interpWithFill, dif_pos he]
end BKAR.Forest
