-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.entries_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:16.578896+00:00
-- url     : https://prove2.me/submissions/bea9a125-6c95-4384-a4a6-d253cd0776e8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_entries_of_generic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_generic

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) : QQRTTEntries :=
  fun P hP => PC.entries_of_generic P fun u v hu hv h0 h1 h2 i j k l =>
    generic P hN hC hM hS hK hP u v hu hv h0 h1 h2 i j k l
end Formalism.FourierDecayAlt.P.Mx6
