-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.flipA_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:17.432814+00:00
-- url     : https://prove2.me/submissions/1aab809d-403d-4a30-865c-1b8872080fe5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
theorem _root_.solution (a : S) : Function.Involutive (flipA a) := by
  intro u
  funext b
  by_cases hb : b = a
  · subst hb; simp [flipA]
  · simp [flipA, Function.update_of_ne hb]
end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
