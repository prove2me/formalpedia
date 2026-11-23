-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_X_sub_C_dvd_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:57.567066+00:00
-- url     : https://prove2.me/submissions/9edb03da-8b2d-4edc-b323-f613b85bf7cc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_division_holds

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
    (hc : c ∈ I) (b : O) (h : (X - C c : O⟦X⟧) ∣ C b) : b = 0 := by
  obtain ⟨y, hy⟩ := h
  have := (linear_division_holds O I c hc).2 y 0 0 b (by rw [← hy]; simp)
  exact this.2.symm
end Formalism.CohomologicalDescent.HeightDescentMinors
