-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.xC_rr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:22.311163+00:00
-- url     : https://prove2.me/submissions/4bc0cbd4-1644-4508-9183-9fc3419d2a72

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xC_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_good0

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
theorem _root_.solution {u : ℂ} (hu : Good P u) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    xC P π u * rr P j u π = xEx P {j} π u := by
  unfold rr
  rw [xC_split P π u hj]
  field_simp [good0 P hu π hj]
end Formalism.FourierDecayAlt.P.Mx6.L4
