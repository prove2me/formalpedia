-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coe_X_sub_C_polynomial_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:18.137829+00:00
-- url     : https://prove2.me/submissions/c4b064d7-4fbd-4f3c-9615-e4b4fa29cc54

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : ((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧) = X - C c := by
  simp
end Formalism.CohomologicalDescent.HeightDescentMinors
