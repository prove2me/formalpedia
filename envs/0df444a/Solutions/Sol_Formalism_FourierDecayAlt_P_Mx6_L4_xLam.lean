-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.xLam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:44.732797+00:00
-- url     : https://prove2.me/submissions/6bf2745d-04f4-4cf5-b296-98d439b7cc1a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_xC_rr

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
theorem _root_.solution {u : ℂ} (hu : Good P u) : xA P u * abelian₂ P u = weightedSumBis P u := by
  unfold abelian₂ weightedSumBis lam xA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, kap_mul]
  refine S_shift P j _ _ fun π π' h => ?_
  show xC P π' u * rr P j u π' = xEx P {j} π u
  rw [xC_rr P hu hj, xEx_up P h {j} (by simp)]
end Formalism.FourierDecayAlt.P.Mx6.L4
