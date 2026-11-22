-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_surjOn_mu_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:06.913799+00:00
-- url     : https://prove2.me/submissions/f4cbbec9-7f6c-4432-aa2b-9bd47b0d8476

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_existsUnique_teichmuller_lift

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
theorem _root_.solution : Set.SurjOn (PadicInt.toZMod (p := l)) (mu l : Set ℤ_[l])
    ((univ.erase (0 : ZMod l) : Finset (ZMod l)) : Set (ZMod l)) := by
  intro x hx
  have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
  obtain ⟨d, ⟨hd, hdx⟩, _⟩ := existsUnique_teichmuller_lift l x hx0
  exact ⟨d, hd, hdx⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
