-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.br_eq_X_mul_const_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:19.085326+00:00
-- url     : https://prove2.me/submissions/8102f871-459e-4cc2-8fa1-f427d5181034

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
theorem _root_.solution (e : ℤ_[l]) :
    ∃ β : O⟦X⟧, br l O e = X * β ∧ constantCoeff β = algebraMap ℤ_[l] O e := by
  refine ⟨_, br_eq_X_mul_shift l O e, ?_⟩
  simp [coeff_one_br]
end Formalism.CohomologicalDescent.HeightDescentMinors
