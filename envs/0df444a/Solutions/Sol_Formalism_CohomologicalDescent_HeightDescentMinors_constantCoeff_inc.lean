-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_inc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:32.414812+00:00
-- url     : https://prove2.me/submissions/445dce03-b14f-48a9-b6ce-dbb2660f24bf

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_algHom_C_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0_eq_zero_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_inc_pi0

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
theorem _root_.solution (hm : MuFacts) (f : O⟦X⟧) : constantCoeff (inc l O f) = constantCoeff f := by
  obtain ⟨Φ, hΦ, hX⟩ := exists_algHom_inc_pi0 l O hm
  rw [hΦ]
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  rw [map_add, map_mul, hX, algHom_C_eq, map_add, map_mul, constantCoeff_pi0_eq_zero_alt l O hm, zero_mul,
    zero_add, constantCoeff_C]
end Formalism.CohomologicalDescent.HeightDescentMinors
