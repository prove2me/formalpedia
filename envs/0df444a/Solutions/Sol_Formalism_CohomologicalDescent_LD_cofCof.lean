-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofCof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:25.710364+00:00
-- url     : https://prove2.me/submissions/680d45e0-5b15-4c12-8eae-60f13c59c853

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_det_eq_pow
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_cofactor_variable
import Theorems.Thm_Formalism_CohomologicalDescent_LD_pow_mul_eval_homogeneous_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : CofCof := by
  intro r
  refine ⟨cofactor_det_eq_pow r, fun N x hx => ?_⟩
  have h := pow_mul_eval_homogeneous_eq ((cofMap r).comp (cofMap r)) (AlgHom.id ℤ _) (genericDet ℤ r) (genericDet ℤ r ^ (r - 1))
    (fun v => cofactor_cofactor_variable r v) N x hx
  rw [← pow_mul] at h
  exact h
end Formalism.CohomologicalDescent.LD
