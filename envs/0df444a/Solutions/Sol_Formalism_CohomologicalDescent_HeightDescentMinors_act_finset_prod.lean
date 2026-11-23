-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.act_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:02.728181+00:00
-- url     : https://prove2.me/submissions/44d1f2ee-a253-4a0b-bae7-11ef0832a05c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_br_padic

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
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {ι : Type*} (c : ℤ_[l]) (s : Finset ι) (f : ι → O⟦X⟧) :
    act l O c (∏ i ∈ s, f i) = ∏ i ∈ s, act l O c (f i) := by
  have ha := hasSubst_br_padic l O c
  simp only [act, ← coe_substAlgHom ha, map_prod]
end Formalism.CohomologicalDescent.HeightDescentMinors
