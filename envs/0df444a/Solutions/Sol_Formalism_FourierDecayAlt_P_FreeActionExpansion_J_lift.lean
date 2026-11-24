-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.J_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:03:57.702147+00:00
-- url     : https://prove2.me/submissions/fa0e9d6d-09eb-4e42-ab1c-f84dfd129337

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution : (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) = lift0 (Formalism.YangianSpanCharacter.T.J A) := by
  have h0 : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := map_zero (Matrix.scalar (Ix S))
  have h1 : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := map_one (Matrix.scalar (Ix S))
  have hn : (io (-1 : A) : SlopeTestRemainingChoices S A) = -1 := by
    rw [show (io (-1 : A) : SlopeTestRemainingChoices S A) = Matrix.scalar (Ix S) (-1 : A) from rfl, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, lift0, h0, h1, hn]
end Formalism.FourierDecayAlt.P.FreeActionExpansion
