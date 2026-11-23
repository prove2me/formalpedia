-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.zf_zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:21.359+00:00
-- url     : https://prove2.me/submissions/3a7557bd-e250-42d3-8404-b2ec12888423

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_ec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_vzb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vcb_vzb

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
theorem _root_.solution : ZF (coord vzb : Fn r) := fun l => ⟨by rw [ec, if_neg (vc_vzb l)], by rw [ec, if_neg (vcb_vzb l)]⟩
end Formalism.FourierDecayAlt.P.Mx2
