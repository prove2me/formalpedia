-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_det_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:57.643048+00:00
-- url     : https://prove2.me/submissions/5ed4d99f-aa94-4241-a338-1e0d400b4322

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_coe_comp_pi0SubstHom

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) {t : ℕ} (M : Matrix (Fin t) (Fin t) O⟦X⟧) :
    jj (inc l O M.det) = (M.map (fun y => jj (inc l O y))).det := by
  have h2 := RingHom.map_det (jj.comp (pi0SubstHom l O)) M
  rw [RingHom.mapMatrix_apply, coe_comp_pi0SubstHom] at h2
  exact h2
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
