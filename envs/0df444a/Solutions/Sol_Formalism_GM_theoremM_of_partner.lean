-- Prove2me | solution 1 for Formalism.GM.theoremM_of_partner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:31.641097+00:00
-- url     : https://prove2.me/submissions/f751182b-e892-4b56-af70-6ee3f8173fe1

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_theoremM_of_point
import Theorems.Thm_Formalism_GM_TM_pointM_of_partner
import Theorems.Thm_Formalism_GM_theoremM_of_point

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
theorem _root_.solution (hMean : M.MeanGam) (hMono : M.WeightSpaceDimMonotone) (hCount : M.MonoCount) (hBad : M.BadCrit)
    (hSmith : SmithZp) (hPart : TM.PartnerM) : M.TheoremM :=
  theoremM_of_point hMean hMono hCount hSmith (TM.pointM_of_partner hBad hPart)
end Formalism.GM
