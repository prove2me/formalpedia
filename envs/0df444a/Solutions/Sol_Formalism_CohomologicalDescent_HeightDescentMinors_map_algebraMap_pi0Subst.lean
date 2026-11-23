-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_pi0Subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:34.204709+00:00
-- url     : https://prove2.me/submissions/3aef108a-505c-4a2a-ac91-2dbbb17131e1

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt

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
theorem _root_.solution (hm : MuFacts) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (inc l ℤ_[l] f) =
      inc l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [inc, inc, map_subst_powerSeries _ (hasSubst_pi0_alt l ℤ_[l]), map_pi0_padic]
end Formalism.CohomologicalDescent.HeightDescentMinors
