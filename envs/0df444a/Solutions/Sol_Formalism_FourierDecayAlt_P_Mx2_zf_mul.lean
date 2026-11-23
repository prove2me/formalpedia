-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.zf_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:38.167132+00:00
-- url     : https://prove2.me/submissions/316ba9a9-fd3f-47ed-950b-ead18e63e624

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
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution {f g : Fn r} (hf : ZF f) (hg : ZF g) : ZF (f * g) := fun l =>
  ⟨by rw [eulerLeibniz, (hf l).1, (hg l).1]; simp, by rw [eulerLeibniz, (hf l).2, (hg l).2]; simp⟩
end Formalism.FourierDecayAlt.P.Mx2
