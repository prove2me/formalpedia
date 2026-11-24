-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_mapC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:41.430566+00:00
-- url     : https://prove2.me/submissions/778cc9b5-4a8c-42f6-901b-f63a7732b8d8

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_res_X

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
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (v : Fin (p + q) × Fin (p + q)) :
    Polynomial.mapAlgHom (res R p q) (Polynomial.C (X v)) = Polynomial.C (resVar R p q v) := by
  rw [Polynomial.coe_mapAlgHom, Polynomial.map_C]
  exact congrArg _ (lrb_res_X R p q v)
end Formalism.CohomologicalDescent.LR
