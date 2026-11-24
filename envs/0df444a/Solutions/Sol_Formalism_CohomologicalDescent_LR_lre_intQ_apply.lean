-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lre_intQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.430798+00:00
-- url     : https://prove2.me/submissions/8304b252-fa27-499c-8054-47707614f40a

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := rfl
end Formalism.CohomologicalDescent.LR
