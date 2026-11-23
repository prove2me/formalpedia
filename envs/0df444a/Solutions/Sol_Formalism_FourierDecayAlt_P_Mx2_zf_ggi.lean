-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.zf_ggi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:31.225689+00:00
-- url     : https://prove2.me/submissions/451a1ba4-7f54-4fbe-a86d-9b71c4833eae

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_vz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vc_vzb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vcb_vz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vcb_vzb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_gamma_inv_vanish

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
theorem _root_.solution (TT : ℝ) : ZF ((gg TT)⁻¹ : Fn r) := fun l =>
  ⟨euler_gamma_inv_vanish _ (vc_vz l) (vc_vzb l) TT, euler_gamma_inv_vanish _ (vcb_vz l) (vcb_vzb l) TT⟩
end Formalism.FourierDecayAlt.P.Mx2
