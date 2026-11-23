-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.X_sub_C_isDistinguished
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:18.904962+00:00
-- url     : https://prove2.me/submissions/2bae6d83-0f20-4758-9db7-69e16341f180

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
theorem _root_.solution (hc : c ∈ I) :
    (Polynomial.X - Polynomial.C c : Polynomial O).IsDistinguishedAt I := by
  refine ⟨⟨fun {n} hn => ?_⟩, Polynomial.monic_X_sub_C c⟩
  rw [Polynomial.natDegree_X_sub_C] at hn
  obtain rfl : n = 0 := by omega
  simpa using hc
end Formalism.CohomologicalDescent.HeightDescentMinors
