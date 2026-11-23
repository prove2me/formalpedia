-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.star_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:35.054793+00:00
-- url     : https://prove2.me/submissions/d99b0206-9495-437d-9118-e087e09d855a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_zeta_mem_function_algebra
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mem_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_zb

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
theorem _root_.solution : star (cc P) = cz P := by
  unfold cc cz; rw [star_mul, star_G, star_zb, fcomm P (mem_G P) (zeta_mem_function_algebra P)]
end Formalism.FourierDecayAlt.P.Mx6
