-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.diagonal_phase_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:09.777442+00:00
-- url     : https://prove2.me/submissions/7aae9315-a820-4bc8-97d7-d2a6334125c9

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.DiagPhase := by
  classical
  intro α F k d hk
  unfold TB.PSDOn at hk ⊢
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hk (Matrix.diagonal fun x : F => d x)
  convert h using 1
  ext x y
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose] <;> ring
end Formalism.FourierDecayAlt.P
