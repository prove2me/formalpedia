-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integralProduct_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:04.965642+00:00
-- url     : https://prove2.me/submissions/50700f5c-bc25-47fe-a438-d7b681cf9626

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_inGLo_nh
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_inGLo_hn
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_kpp_nh
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_kpp_hn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.IntegralProduct := by
  intro o _ _ _ k0 _ _ _ r k n h hn hh
  exact ⟨S3x3.inGLo_nh o hn hh, S3x3.inGLo_hn o hn hh, S3x3.kpp_nh o hn hh, S3x3.kpp_hn o hn hh⟩
end Formalism.FourierDecayAlt.P
