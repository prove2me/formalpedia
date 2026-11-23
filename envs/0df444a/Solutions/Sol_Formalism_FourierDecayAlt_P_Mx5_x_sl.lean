-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.x_sl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:09.829895+00:00
-- url     : https://prove2.me/submissions/d77256ee-e9ad-49bf-996b-2b5478a72abd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_x_iv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    xA P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j = weightedSumBis P Y := by
  unfold weightedSumBis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, x_iv P Y hx j hj]
  exact kap_ss P j _ (fun π π' h => xEx_up P j {j} (Finset.mem_singleton_self j) Y π π' h)
end Formalism.FourierDecayAlt.P.Mx5
