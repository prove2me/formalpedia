-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.compC_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:19.903895+00:00
-- url     : https://prove2.me/submissions/1b746645-d20f-41ab-ba55-b8c5bc633216

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sh_same
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_TT_eq

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
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ) :
    (SS P l * kap P fun π => xEx P {l} π u) * (SS P l * kap P fun π => xEx P {l} π v) =
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P l * kap P fun π => xEx P {l} π u) := by
  rw [TT_eq P l l _ _ _ (sh_same hSh hR P l {l} (Finset.mem_singleton_self l) u),
    TT_eq P l l _ _ _ (sh_same hSh hR P l {l} (Finset.mem_singleton_self l) v), mul_comm]
end Formalism.FourierDecayAlt.P.Mx7
