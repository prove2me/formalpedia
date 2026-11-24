-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrfc_Phi_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:30.986798+00:00
-- url     : https://prove2.me/submissions/c49ce6f8-6db0-4181-8b8d-45f522a4ddf5

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle

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
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (l :: w) G = lrfc_tau l (lrfc_Phi w G) := rfl
end Formalism.CohomologicalDescent.LR
