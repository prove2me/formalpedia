-- Prove2me | solution 1 for BKAR.Forest.hasDerivAt_interpWithFill_apply_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:19.307871+00:00
-- url     : https://prove2.me/submissions/9d62f70f-c57b-4fa8-8bba-9f009635ee72

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_interpWithFill_of_mem_activeEdges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 1 t := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) = fun s : ℝ => s := by
    funext s
    exact F.interpWithFill_of_mem_activeEdges u s he
  rw [hfun]
  exact hasDerivAt_id t
end BKAR.Forest
