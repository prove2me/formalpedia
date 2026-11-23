-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.sh_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:19.046584+00:00
-- url     : https://prove2.me/submissions/6d76ee51-bdab-47f9-8b04-f19d2afc9f72

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_pair
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_rho_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xEx_up


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (P : Par) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (Y : ℂ) :
    (kap P fun π => xEx P {l} π Y) * SS P j = SS P j * kap P fun π => xEx P {l, j} π Y * (Y + 1 + (rho P π j : ℂ)) :=
  hSh P j _ _ (fun π π' hU => by
    show xEx P {l} π' Y = _
    rw [xEx_pair P π' Y l j hj hjl, xEx_up hR P j π π' hU {l, j} (by simp), rho_up hR P j hj π π' hU]
    push_cast; ring)
end Formalism.FourierDecayAlt.P.Mx7
