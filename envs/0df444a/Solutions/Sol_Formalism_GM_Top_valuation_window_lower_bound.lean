-- Prove2me | solution 1 for Formalism.GM.Top.valuation_window_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:58.79786+00:00
-- url     : https://prove2.me/submissions/37c0e850-74c7-497b-976f-d2d22ff46e6a

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MahlerK
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithBall
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Theorems.Thm_Formalism_GM_Top_lieMat
import Theorems.Thm_Formalism_GM_Top_lieRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.Top
open Formalism.GM
namespace Formalism.GM.Top
theorem _root_.solution : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
