-- Prove2me | solution 1 for Formalism.GM.theoremM_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:27.972467+00:00
-- url     : https://prove2.me/submissions/9f0d2d35-2a6b-438b-a9ba-98ed0b4c191a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_existsAdaptedBasis
import Theorems.Thm_Formalism_GM_TM_theoremM_of_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution (hMean : M.MeanGam) (hMono : M.WeightSpaceDimMonotone) (hCount : M.MonoCount) (hSmith : SmithZp)
    (hPt : TM.PointM) : M.TheoremM :=
  TM.theoremM_of_point hMean hMono hCount hSmith TM.existsAdaptedBasis hPt
end Formalism.GM
