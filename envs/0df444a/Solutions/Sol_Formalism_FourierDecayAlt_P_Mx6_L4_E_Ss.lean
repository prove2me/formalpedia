-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.E_Ss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:44.261566+00:00
-- url     : https://prove2.me/submissions/50419db1-0fa3-4853-9123-37aab0093b7e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ss_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_up

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L4
theorem _root_.solution (l : ℕ) (u : ℂ) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) = star (SS P l) * kap P fun π => xEx P {l} π u :=
  (Ss_shift P l (fun π => xEx P {l} π u) (fun π => xEx P {l} π u)
    fun _ _ h => xEx_up P h {l} (Finset.mem_singleton_self l) u).symm
end Formalism.FourierDecayAlt.P.Mx6.L4
