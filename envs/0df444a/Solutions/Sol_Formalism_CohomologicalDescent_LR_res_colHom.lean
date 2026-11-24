-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_colHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:24.553626+00:00
-- url     : https://prove2.me/submissions/84e083c7-f181-4cf7-9d1b-2086616ff83e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_aeval_hom
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_proj
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_col

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
theorem _root_.solution (μ : Fin (p + q) → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f μ) :
    IsWeightedHomogeneous (colW q q) (res R p q f) (fun b => μ (Fin.natAdd p b)) :=
  lrb_aeval_hom R (colW q q) (resVar R p q) _ (lrb_var_col R p q) f _ (lrb_proj R (lrbPi p q) _ f μ hf)
end Formalism.CohomologicalDescent.LR
