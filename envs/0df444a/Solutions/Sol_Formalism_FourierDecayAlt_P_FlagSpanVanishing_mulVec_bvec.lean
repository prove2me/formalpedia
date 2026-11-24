-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagSpanVanishing.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:31:37.085106+00:00
-- url     : https://prove2.me/submissions/1b89cf23-e39c-4d6f-abff-218d2f39c98c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagSpanVanishing
theorem _root_.solution (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by
  funext i; simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.P.FlagSpanVanishing
