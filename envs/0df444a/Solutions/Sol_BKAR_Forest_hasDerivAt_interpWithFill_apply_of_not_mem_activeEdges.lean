-- Prove2me | solution 1 for BKAR.Forest.hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:44.132871+00:00
-- url     : https://prove2.me/submissions/e54cabcc-cfd0-4d2b-918b-cee731528aba

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_interpWithFill_of_inSameComponent

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∉ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 0 t := by
  have hsame : F.inSameComponent e.left e.right := by
    by_contra hdiff
    exact he ((F.mem_activeEdges_iff).mpr hdiff)
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) =
        fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right hsame) := by
    funext s
    exact F.interpWithFill_of_inSameComponent u s hsame
  rw [hfun]
  exact hasDerivAt_const t _
end BKAR.Forest
