-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.ep_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:28.749046+00:00
-- url     : https://prove2.me/submissions/b89c9872-e5b4-480a-b4c3-005658bab7f6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (p : Fin (2 * r + k + 1)) : ep p * ep p = 1 := by
  unfold ep
  rw [← mul_pow]
  norm_num
end Formalism.FourierDecayAlt.P.PBG
