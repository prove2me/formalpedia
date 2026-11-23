-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.leading_coeff_l0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:21.153452+00:00
-- url     : https://prove2.me/submissions/ea0ec8b3-a8d4-4e4c-bf24-cda264166a56

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_lin

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
theorem _root_.solution : Lead 1 (-(zbA P * ggiA P)) (l0A P) := by
  refine (Lead.lin (-nabA P - (1 / 2 : ℂ) • (zbA P * ggiA P)) (-(zbA P * ggiA P))).congr rfl rfl fun Y => ?_
  unfold l0A
  rw [← Algebra.smul_def, add_smul, smul_neg]
  abel
end Formalism.FourierDecayAlt.P.Mx5
