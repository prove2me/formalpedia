-- Prove2me | solution 1 for Formalism.CountingSumsFrames.partnerM_of_tieOps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:30.626977+00:00
-- url     : https://prove2.me/submissions/4198fd93-81cd-4dc1-9b9a-ec07001947cd

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_partnerM_of_parts
import Theorems.Thm_Formalism_CountingSumsFrames_partner_condition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
namespace Formalism.CountingSumsFrames
theorem _root_.solution (hTie : TieOps) : PartnerM := partnerM_of_parts hTie partner_condition
end Formalism.CountingSumsFrames
