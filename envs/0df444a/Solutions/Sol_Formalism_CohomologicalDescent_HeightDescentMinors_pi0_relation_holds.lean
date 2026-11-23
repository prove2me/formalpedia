-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.pi0_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.247696+00:00
-- url     : https://prove2.me/submissions/315db7cf-b06c-45d3-9e8d-a96ac2544746

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_algebraMap_padicInt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_phi_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r5_frobenius_holds

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
theorem _root_.solution : FrobeniusPiZero := by
  intro l _ O _ _
  obtain ⟨r, hr⟩ := r5_frobenius_holds l (pi0 l ℤ_[l])
  refine ⟨PowerSeries.map (algebraMap ℤ_[l] O) r, ?_⟩
  have h := congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hr
  rw [map_phi_padic, map_pi0_algebraMap_padicInt] at h
  simpa [map_pi0_algebraMap_padicInt] using h
end Formalism.CohomologicalDescent.HeightDescentMinors
