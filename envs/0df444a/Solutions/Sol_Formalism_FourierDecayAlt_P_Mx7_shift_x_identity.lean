-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.shift_x_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:52.710958+00:00
-- url     : https://prove2.me/submissions/e2c921a8-d9f7-4aa8-8163-87c9559a141d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xC_eq
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
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (Y : ℂ) :
    xA P Y * SS P l = SS P l * kap P fun π => xEx P {l} π Y * (Y + 1 + (rho P π l : ℂ)) :=
  hSh P l _ _ (fun π π' hU => by
    show xC P π' Y = _
    rw [xC_eq P π' Y l hl, xEx_up hR P l π π' hU {l} (Finset.mem_singleton_self l), rho_up hR P l hl π π' hU]
    push_cast; ring)
end Formalism.FourierDecayAlt.P.Mx7
