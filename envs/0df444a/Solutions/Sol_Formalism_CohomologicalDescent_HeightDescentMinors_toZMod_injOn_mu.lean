-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_injOn_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:31.34381+00:00
-- url     : https://prove2.me/submissions/50f5143e-84ed-4a20-bd7c-605343cc9a47

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_existsUnique_teichmuller_lift
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_ne_zero_of_mem_mu

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
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : Set.InjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l]) := by
  intro x hx y hy hxy
  exact (existsUnique_teichmuller_lift l _ (toZMod_ne_zero_of_mem_mu l hx)).unique ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
