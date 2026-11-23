-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.qPositive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.923012+00:00
-- url     : https://prove2.me/submissions/61aa679d-75cf-4620-a479-979939f9ca67

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_q_core

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
theorem _root_.solution : QPositive := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core k u u' ρ l Y hl1 hlk h hA
    · have := q_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
      rwa [prod_congr rfl (fun i _ => mul_comm (Y + 1/2 + u' i) (Y + 1/2 + u i))] at this
  unfold qpoly
  nlinarith
end Formalism.FourierDecayAlt.P.Interlace
