-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_coeffT_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:32.335845+00:00
-- url     : https://prove2.me/submissions/880434e9-c2b7-4325-a226-d882c5be7d02

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
theorem _root_.solution (d : Fin r × Fin n →₀ ℕ)
    (G H : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (G + H) = lrfc_coeffT d G + lrfc_coeffT d H := by
  ext m
  simp [lrfc_coeff_coeffT]
end Formalism.CohomologicalDescent.LR
