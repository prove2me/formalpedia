-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.scalInv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:04.652956+00:00
-- url     : https://prove2.me/submissions/037244c4-d443-4dbb-8246-d4db8b31d951

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (c : ℝ) (hc : c ≠ 0) (x : V) : (scalInv V c hc).symm x = c • x := rfl
end Formalism.FourierDecayAlt.P.S6x5
