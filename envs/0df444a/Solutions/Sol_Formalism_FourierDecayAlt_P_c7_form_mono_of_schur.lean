-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c7_form_mono_of_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:37.929829+00:00
-- url     : https://prove2.me/submissions/f28383d6-0618-48ac-93dc-0627d2b26c52

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative
import Theorems.Thm_Formalism_FourierDecayAlt_P_c7_form_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.FormMonoOfSchur := fun _ => c7_form_mono
end Formalism.FourierDecayAlt.P
