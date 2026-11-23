-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_term_upper_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:23.3828+00:00
-- url     : https://prove2.me/submissions/35896415-ae8d-4b0e-aefc-3ad24ea7cfae

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_xEx

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
theorem _root_.solution (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P) (S12 P) := by
  refine (Lead.sum (Icc 1 (P.k - 1)) (fun l Y => (kap P fun π => xEx P {l} π Y) * star (SS P l))
    fun l _ => ?_).congr rfl rfl fun Y => rfl
  exact ((lead_xEx P {l} m hm).mul_const (star (SS P l))).congr rfl (zero_mul _) fun Y => rfl
end Formalism.FourierDecayAlt.P.Mx5
