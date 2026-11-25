-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corner_invariant_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:44:14.173096+00:00
-- url     : https://prove2.me/submissions/6d3f5370-7d5d-4626-ab60-ff4ebd234a5f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_corner_invariant

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CornerInvariant := by
  intro A _ r v₂ X v₁ h₂ h₁ l hl
  exact corner_invariant h₂ h₁ l hl
end Formalism.FourierDecayAlt.P
