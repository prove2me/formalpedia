-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.eulerComm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:04.053987+00:00
-- url     : https://prove2.me/submissions/2fa4528e-d974-47c5-a677-36c6c7afc5d5

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

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
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution : EulerComm := by
  intro r v w
  ext f γ
  simp only [Module.End.mul_apply, euler, LinearMap.coe_mk, AddHom.coe_mk]
  ring
end Formalism.FourierDecayAlt.P.Mx2
