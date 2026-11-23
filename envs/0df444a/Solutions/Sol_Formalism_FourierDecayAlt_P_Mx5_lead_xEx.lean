-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lead_xEx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:31:57.84684+00:00
-- url     : https://prove2.me/submissions/b2e6e149-117c-4d90-94a2-fee741373062

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_card_I

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
theorem _root_.solution (ex : Finset ℕ) (m : ℕ) (hm : P.k - 1 < m) :
    Lead m (0 : A P) fun Y => kap P fun π => xEx P ex π Y := ((lead_prod P (Icc 1 (P.k - 1) \ ex)).lt
    (lt_of_le_of_lt ((Finset.card_le_card Finset.sdiff_subset).trans (card_I P).le) hm)).congr rfl rfl
    fun Y => rfl
end Formalism.FourierDecayAlt.P.Mx5
