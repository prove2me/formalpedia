-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_phi_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:52.498044+00:00
-- url     : https://prove2.me/submissions/3b16a9c1-bdf3-4afe-854d-414e997ca825

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_subst_powerSeries
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_one_add_X_pow_sub_one_alt

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
theorem _root_.solution (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (phi l ℤ_[l] f) =
      phi l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by
  rw [phi, phi, map_subst_powerSeries _ (hasSubst_one_add_X_pow_sub_one_alt l)]
  simp
end Formalism.CohomologicalDescent.HeightDescentMinors
