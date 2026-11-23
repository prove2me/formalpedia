-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_comp_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:31.627307+00:00
-- url     : https://prove2.me/submissions/0790ca46-87bd-40b7-9375-5ea4849587d2

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_binomialSeriesSubOne

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (c d : ℤ_[l]) (f : O⟦X⟧) :
    act l O c (act l O d f) = act l O (d * c) f := by
  have e := binomialAction_binomialSeriesSubOne l O c d
  rw [act] at e
  rw [act, act, act, PowerSeries.subst_comp_subst_apply (hasSubst_br_padic l O d) (hasSubst_br_padic l O c), e]
end Formalism.CohomologicalDescent.HeightDescentMinors
