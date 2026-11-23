-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:39.352931+00:00
-- url     : https://prove2.me/submissions/d2160bad-0722-4a7b-b3b6-d5a500001118

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_ratio_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution : InterlaceRatio := by
  intro k u u' ρ l Y hl1 hlk h hc
  rcases hc with hA | hB
  · exact ratio_core k u u' ρ l Y hl1 hlk h hA
  · have := ratio_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
    rwa [mul_comm (|Y + 1/2 + u' l|), mul_comm (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))] at this
end Formalism.FourierDecayAlt.P.Interlace
