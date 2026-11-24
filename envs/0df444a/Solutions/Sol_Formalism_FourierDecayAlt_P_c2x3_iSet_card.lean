-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_iSet_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:39.465138+00:00
-- url     : https://prove2.me/submissions/d5689ab1-6ae5-4151-9bad-e396e679cfb1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact

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
theorem _root_.solution {m a : ℕ} (h : a ≤ m) : (C2.iSet m a).card = a := by
  unfold C2.iSet
  rw [Fin.card_filter_val_lt]; omega
end Formalism.FourierDecayAlt.P
