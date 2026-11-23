-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_binomialSeriesSubOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:47.057398+00:00
-- url     : https://prove2.me/submissions/349abf3c-fec9-4272-9251-a299c7f8d415

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeries_sub_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeries_subst_sub_one_eq_mul

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
theorem _root_.solution (c d : ℤ_[l]) : act l O c (br l O d) = br l O (d * c) := by
  have hs := hasSubst_binomialSeries_sub_one (R := ℤ_[l]) (A := O) c
  simp only [act, br]
  rw [← PowerSeries.coe_substAlgHom hs, map_sub, map_one, PowerSeries.coe_substAlgHom, binomialSeries_subst_sub_one_eq_mul]
end Formalism.CohomologicalDescent.HeightDescentMinors
