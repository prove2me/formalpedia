-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.sh_same
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:19.180699+00:00
-- url     : https://prove2.me/submissions/f8d1a2b2-172b-4427-b7dd-5c3dcaa41c77

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_xEx_up
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
theorem _root_.solution (hSh : SSShift) (hR : RhoUp) (P : Par) (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) :
    (kap P fun π => xEx P ex π Y) * SS P l = SS P l * kap P fun π => xEx P ex π Y :=
  hSh P l _ _ (fun π π' hU => xEx_up hR P l π π' hU ex hl Y)
end Formalism.FourierDecayAlt.P.Mx7
