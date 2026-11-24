-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.sgn_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:42.352501+00:00
-- url     : https://prove2.me/submissions/e17ad6b5-1a94-4099-b36b-eed2002a3b22

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums

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
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val) : GBasic.sgn k r p = 1 := by
  unfold GBasic.sgn
  rw [if_neg (show ¬ p.val = r + k by omega)]
end Formalism.FourierDecayAlt.P.UnipotentSums
