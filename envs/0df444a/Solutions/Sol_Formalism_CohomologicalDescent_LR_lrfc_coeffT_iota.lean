-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_coeffT_iota
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:32.671827+00:00
-- url     : https://prove2.me/submissions/0f9f00b2-ada2-44aa-a8a0-1ec31c42599e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeff_coeffT
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
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ) (F : MvPolynomial (Fin r × Fin n) R) :
    lrfc_coeffT d (lrfc_iota F) = if d = 0 then F else 0 := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, lrfc_iota, coeff_map, coeff_C]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
end Formalism.CohomologicalDescent.LR
