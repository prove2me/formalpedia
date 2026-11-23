-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.br_eq_X_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:19.036809+00:00
-- url     : https://prove2.me/submissions/127ad579-7d24-4cea-8bb7-c57428144a4e

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_br_eq_X_mul_shift
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_one_br

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
theorem _root_.solution (c : ℤ_[l]) :
    ∃ s : O⟦X⟧, br l O c = X * s ∧ constantCoeff s = algebraMap ℤ_[l] O c := by
  refine ⟨_, br_eq_X_mul_shift l O c, ?_⟩
  simp [coeff_one_br]
end Formalism.CohomologicalDescent.HeightDescentMinors
