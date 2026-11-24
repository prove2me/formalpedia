-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.polynomial_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:51.412929+00:00
-- url     : https://prove2.me/submissions/f58a9137-8405-46be-90b3-b13e1c7afb5a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_polyVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.PolyVanish := by
  intro X _ _ d c F h
  exact Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.polyVanish d c F h
end Formalism.FourierDecayAlt.P
