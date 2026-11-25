-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_kernel_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:20.231921+00:00
-- url     : https://prove2.me/submissions/e55f3fa5-0aa5-4ea3-93c0-4c98b50643b2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx10_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))
end Formalism.FourierDecayAlt.P
