-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_applyWord_append_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:31.243204+00:00
-- url     : https://prove2.me/submissions/3bf3cd3b-08a0-4317-bff7-87fed49a5ed6

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
theorem _root_.solution (w : List (Fin r × Fin r × ℕ)) (x : Fin r × Fin r × ℕ)
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (w ++ [x]) F = applyWord R w (rowDiv R x.1 x.2.1 x.2.2 F) := by
  simp [applyWord, List.foldr_append]
end Formalism.CohomologicalDescent.LR
