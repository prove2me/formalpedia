-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.roots_outside_jointly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:18.694058+00:00
-- url     : https://prove2.me/submissions/adb1111d-90d6-45c0-acf5-ec9de8cb6197

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_lambda_side_inequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.RootsOutJoint := by
  unfold C7.RootsOutJoint LE.Sys.RootsOut
  intro S u u' l hl hlk hI hI' hB s hs
  have hb := hB _ hs
  have key := lambda_side_inequality S.k S.r u u' S.lam l (-S.lam s) hl hlk hI hI' hb s
  unfold C7.Between at hb
  rw [neg_neg] at hb
  by_cases h : l ≤ s.val + 1
  · have := key.1 h
    linarith [hb.1]
  · have := key.2 (by omega)
    linarith [hb.2]
end Formalism.FourierDecayAlt.P
