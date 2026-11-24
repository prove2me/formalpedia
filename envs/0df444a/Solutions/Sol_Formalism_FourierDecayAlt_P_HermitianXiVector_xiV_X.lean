-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.xiV_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:54.536259+00:00
-- url     : https://prove2.me/submissions/98786326-298c-4ac5-be09-fa8ed8159bbe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector

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
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → C2.xiV k r ξ i = 0 := by
  intro i hi
  unfold C2.xiV
  split_ifs with h
  · exact absurd h (by omega)
  · rfl
end Formalism.FourierDecayAlt.P.HermitianXiVector
