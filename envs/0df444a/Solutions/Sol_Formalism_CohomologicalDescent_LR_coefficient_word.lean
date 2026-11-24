-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.coefficient_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:28.667818+00:00
-- url     : https://prove2.me/submissions/d0cd514d-aa3f-4874-99aa-f5ab83f533cc

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_Phi
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_vars
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_nodup
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_wordOf
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_eval_Phi
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_eval_coeffT
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_coeff_ell
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
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution : CoeffWord := by
  intro R _ r n ν F e hF he hcol
  classical
  have hd : ∀ (a : Fin r) (s : Fin n), s.val < a.val → lrf_off e (a, s) = e (a, s) := by
    intro a s h
    simp [lrf_off, Finsupp.filter_apply, h]
  have h1 := lrfc_coeffT_Phi (lrf_L r n) lrf_nodup F (lrf_off e)
  have hc : ∀ u, u ∉ (lrf_L r n).map (·.2.2) → lrf_off e u = 0 := by
    intro u hu
    rw [lrf_mem_vars] at hu
    simp [lrf_off, Finsupp.filter_apply, hu]
  rw [if_pos hc, lrf_wordOf e (lrf_off e) hd] at h1
  rw [← h1, lrf_eval_coeffT, lrf_eval_Phi, lrf_coeff_ell ν F e hF he hcol]
end Formalism.CohomologicalDescent.LR
