-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.rv_rv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:06:20.29246+00:00
-- url     : https://prove2.me/submissions/bb8fe65b-159b-4f3f-9117-1e68f69e2b0d

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
theorem _root_.solution (p : Fin (2 * r + k + 1)) : rv (rv p) = p := Fin.rev_rev p
end Formalism.FourierDecayAlt.P.PBG
