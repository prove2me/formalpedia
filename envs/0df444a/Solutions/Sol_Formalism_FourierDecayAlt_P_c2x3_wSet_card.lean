-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_wSet_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:34.966795+00:00
-- url     : https://prove2.me/submissions/7e3ed595-bc7d-49ae-9b57-2b815224a4ad

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_iSet_card

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
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m a : ℕ} (w : Equiv.Perm (Fin m)) (h : a ≤ m) : (C2.wSet w a).card = a := by
  unfold C2.wSet
  rw [Finset.card_image_of_injective _ w.injective, c2x3_iSet_card h]
end Formalism.FourierDecayAlt.P
