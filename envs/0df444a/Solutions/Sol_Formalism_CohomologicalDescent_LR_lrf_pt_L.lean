-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_pt_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:22.336085+00:00
-- url     : https://prove2.me/submissions/8b8d31b5-a165-49af-a17d-4f9c09cbca4e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_L
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_vars
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pairwise
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (v : Fin r × Fin n) :
    eval (lrf_idS R r n) (lrfc_Phi (lrf_L r n) (X v)) = lrf_ell R r n v := by
  rw [lrf_pt (lrf_L r n) lrf_pairwise (fun l hl => ⟨((lrf_mem_L l).1 hl).1, ((lrf_mem_L l).1 hl).2.2⟩) v]
  simp only [lrf_mem_vars, lrf_ell]
end Formalism.CohomologicalDescent.LR
