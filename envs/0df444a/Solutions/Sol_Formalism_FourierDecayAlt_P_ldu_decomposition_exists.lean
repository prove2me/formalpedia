-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ldu_decomposition_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:00.940791+00:00
-- url     : https://prove2.me/submissions/49cffb41-e6ae-4416-8187-755e6a36ad80

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_ldu_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_ldu_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.S3x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.LDUExists := by
  intro A _ r M hM
  obtain ⟨L, U, d, hL, hU, e⟩ := ldu_exists r M hM
  refine ⟨L, U, d, hL, hU, e, fun l hl => ?_⟩
  rw [e]
  exact lead_ldu_succ d hL hU l hl
end Formalism.FourierDecayAlt.P
