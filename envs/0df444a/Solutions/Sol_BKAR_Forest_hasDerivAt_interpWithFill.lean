-- Prove2me | solution 1 for BKAR.Forest.hasDerivAt_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:00.583671+00:00
-- url     : https://prove2.me/submissions/14e6db23-bc5c-448e-a5e6-ee3f27be4ae1

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_activeDirection_apply_of_mem
import Theorems.Thm_BKAR_Forest_activeDirection_apply_of_not_mem
import Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill_apply_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s)
      F.activeDirection t := by
  rw [hasDerivAt_pi]
  intro e
  by_cases he : e ∈ F.activeEdges
  · rw [F.activeDirection_apply_of_mem he]
    exact F.hasDerivAt_interpWithFill_apply_of_mem_activeEdges u he t
  · rw [F.activeDirection_apply_of_not_mem he]
    exact F.hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges u he t
end BKAR.Forest
