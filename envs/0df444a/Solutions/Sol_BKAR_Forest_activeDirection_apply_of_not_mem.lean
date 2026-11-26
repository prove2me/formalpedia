-- Prove2me | solution 1 for BKAR.Forest.activeDirection_apply_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:24.110946+00:00
-- url     : https://prove2.me/submissions/fbe57937-aa52-4de8-8fe9-d935bff4fef8

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_edgeBasis_of_ne


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∉ F.activeEdges) :
    F.activeDirection e = 0 := by
  rw [activeDirection]
  rw [Finset.sum_apply]
  classical
  exact Finset.sum_eq_zero fun e' he' => by
    have hne : e ≠ e' := by
      intro h
      exact he (h.symm ▸ he')
    exact edgeBasis_of_ne hne
end BKAR.Forest
