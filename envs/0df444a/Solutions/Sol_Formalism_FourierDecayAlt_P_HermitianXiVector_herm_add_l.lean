-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.herm_add_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:41.60022+00:00
-- url     : https://prove2.me/submissions/f414eee3-4bbf-4b5c-be81-0c9e6069dc44

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b w : Fin n → ℂ) :
    herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, mulVec_add, dotProduct_add]
end Formalism.FourierDecayAlt.P.HermitianXiVector
