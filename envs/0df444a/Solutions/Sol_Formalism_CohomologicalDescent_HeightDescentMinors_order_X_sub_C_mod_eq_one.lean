-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.order_X_sub_C_mod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:12.115951+00:00
-- url     : https://prove2.me/submissions/fcde8734-0447-41e6-a2bb-a8789334e506

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coe_X_sub_C_polynomial_powerSeries
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_ideal_ne_top_alt

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
variable {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (hc : c ∈ I) :
    ((((Polynomial.X - Polynomial.C c : Polynomial O) : O⟦X⟧).map
      (Ideal.Quotient.mk I)).order.toNat) = 1 := by
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ideal_ne_top_alt I)
  rw [coe_X_sub_C_polynomial_powerSeries, map_sub, PowerSeries.map_X, PowerSeries.map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero, sub_zero, order_X]
  rfl
end Formalism.CohomologicalDescent.HeightDescentMinors
