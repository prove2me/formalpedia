-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.cf_cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:56.642606+00:00
-- url     : https://prove2.me/submissions/a06fbce0-f759-4e06-82d5-459a5d62ea69

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_ec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vcb_vz
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
theorem _root_.solution (m : Fin r) : CF (coord (vcb m) : Fn r) := ⟨by rw [ec, if_neg (vcb_vz m).symm], by rw [ec, if_neg (vcb_vzb m).symm]⟩
end Formalism.FourierDecayAlt.P.Mx2
