-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_Phi_append_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:01.09842+00:00
-- url     : https://prove2.me/submissions/072f2b37-7e44-4a76-8e34-736cf61cbc28

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (l : Fin r × Fin r × (Fin r × Fin n))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (w ++ [l]) G = lrfc_Phi w (lrfc_tau l G) := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [List.cons_append, lrfc_Phi_cons, ih, lrfc_Phi_cons]
end Formalism.CohomologicalDescent.LR
