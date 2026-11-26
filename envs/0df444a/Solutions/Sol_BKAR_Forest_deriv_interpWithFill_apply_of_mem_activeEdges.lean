-- Prove2me | solution 1 for BKAR.Forest.deriv_interpWithFill_apply_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:08.480203+00:00
-- url     : https://prove2.me/submissions/2f350c15-1ecd-4b64-9c09-589d99477ccc

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_deriv_interpWithFill_apply_of_not_inSameComponent

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 :=
  F.deriv_interpWithFill_apply_of_not_inSameComponent u
    (F.not_inSameComponent_of_mem_activeEdges he) t
end BKAR.Forest
