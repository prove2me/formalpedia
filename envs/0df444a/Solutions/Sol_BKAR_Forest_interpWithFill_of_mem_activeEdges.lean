-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:30.843109+00:00
-- url     : https://prove2.me/submissions/c6fc472b-c6d2-46a9-9f0b-ab8e47797ebc

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_interpWithFill_of_not_inSameComponent


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    F.interpWithFill u t e = t :=
  F.interpWithFill_of_not_inSameComponent u t
    (F.not_inSameComponent_of_mem_activeEdges he)
end BKAR.Forest
