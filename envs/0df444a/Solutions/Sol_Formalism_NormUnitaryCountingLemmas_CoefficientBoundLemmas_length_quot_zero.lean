-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas.length_quot_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:57.404149+00:00
-- url     : https://prove2.me/submissions/6c484b38-fb29-4563-b65c-68dc1e3d51f4

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_CoefficientBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
theorem _root_.solution : Module.length R (R ⧸ Ideal.span ({0} : Set R)) = ⊤ := by
  have := Ring.ord_eq_addVal (R := R) 0
  simpa [Ring.ord] using this
end Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
