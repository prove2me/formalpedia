-- Prove2me | solution 1 for Formalism.MainNotions.G.WittPI.wittIdent_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:12.071569+00:00
-- url     : https://prove2.me/submissions/31eef240-62c1-45eb-a3a1-206a6a755c1a

import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_WittIdentPI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.WittPI
namespace Formalism.MainNotions.G.WittPI
theorem _root_.solution (H : PI.WittUnram) : Formalism.MainNotions.G.WittIdent :=
  fun p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS =>
    H p n' W Qq σ hS.frac_alt hS.p_unif hS.res_card hS.eq_sum_herm_smul_frame_of_inW hS.frob
end Formalism.MainNotions.G.WittPI
