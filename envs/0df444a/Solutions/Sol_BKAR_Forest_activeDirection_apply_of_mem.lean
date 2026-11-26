-- Prove2me | solution 1 for BKAR.Forest.activeDirection_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:09.638802+00:00
-- url     : https://prove2.me/submissions/a559e7ca-66b3-457c-8c31-5603ce61e580

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_edgeBasis_of_ne
import Theorems.Thm_BKAR_edgeBasis_self
attribute [local simp] BKAR.edgeBasis_self



set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    F.activeDirection e = 1 := by
  rw [activeDirection]
  rw [Finset.sum_apply]
  classical
  calc
    (Finset.sum F.activeEdges fun e' => edgeBasis e' e) =
        edgeBasis e e := by
          exact Finset.sum_eq_single_of_mem e he (fun e' _ hne => by
            exact edgeBasis_of_ne hne.symm)
    _ = 1 := edgeBasis_self e
end BKAR.Forest
