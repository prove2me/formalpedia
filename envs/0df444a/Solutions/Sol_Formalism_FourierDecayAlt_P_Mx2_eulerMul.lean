-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.eulerMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:37.589912+00:00
-- url     : https://prove2.me/submissions/9d445e78-7bfa-4275-a3b7-7c369d7c25c2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerLeibniz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : EulerMul := by
  intro r v f
  ext g : 1
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [eulerLeibniz, add_comm]
end Formalism.FourierDecayAlt.P.Mx2
