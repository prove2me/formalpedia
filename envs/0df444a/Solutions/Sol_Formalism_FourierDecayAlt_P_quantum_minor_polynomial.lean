-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quantum_minor_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:59:47.205865+00:00
-- url     : https://prove2.me/submissions/34c2bb13-54b3-4c8e-bc14-056b18e978e0

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_qminor_isPol

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
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.QminorPoly := by
  intro A _ _ n t E a b
  exact Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.qminor_isPol E a b
end Formalism.FourierDecayAlt.P
