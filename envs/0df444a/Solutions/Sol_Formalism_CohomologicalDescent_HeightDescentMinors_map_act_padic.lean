-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_act_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:52.478797+00:00
-- url     : https://prove2.me/submissions/d8228584-ea29-4e2b-a6f8-165646daea49

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_algebraMap_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries

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
theorem _root_.solution (c : ℤ_[l]) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (act l ℤ_[l] c f) =
      act l O c (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [act, act, map_subst_powerSeries _ (hasSubst_br_padic l ℤ_[l] c), map_algebraMap_binomialSeriesSubOne]
end Formalism.CohomologicalDescent.HeightDescentMinors
