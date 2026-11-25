-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.qPositiveShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:58.684427+00:00
-- url     : https://prove2.me/submissions/3acdf251-6df8-4ae5-a153-fc9b5120e750

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr2_q_core__291ef32df1e7
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr2_q_core___1e3bfb2e6a63

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution : QPositiveShift := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core' k u u' ρ l Y hl1 hlk h hA
    · exact q_core'' k u u' ρ l Y hl1 hlk h hB
  unfold qpoly
  nlinarith
end Formalism.FourierDecayAlt.P.Fr2
