-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.sgn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:23.953864+00:00
-- url     : https://prove2.me/submissions/64dc8a31-9334-4628-b921-b5bf863806e0

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (k : ℕ) (T : A) :
    (((-1 : ℤ) ^ k : ℤ) : A) * T = ((-1 : ℂ) ^ k) • T := by
  simp [Algebra.smul_def]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
