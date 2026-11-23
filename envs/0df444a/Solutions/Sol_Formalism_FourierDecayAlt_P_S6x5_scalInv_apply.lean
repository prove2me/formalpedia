-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.scalInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:45.475573+00:00
-- url     : https://prove2.me/submissions/e4035618-74da-4544-9574-1e891d041a77

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
theorem _root_.solution (c : ℝ) (hc : c ≠ 0) (x : V) : scalInv V c hc x = c⁻¹ • x := rfl
end Formalism.FourierDecayAlt.P.S6x5
