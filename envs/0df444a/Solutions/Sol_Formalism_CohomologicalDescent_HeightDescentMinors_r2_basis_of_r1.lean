-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r2_basis_of_r1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:03.076834+00:00
-- url     : https://prove2.me/submissions/66f27df5-8a7e-47d2-914d-6c6e6a444d1b

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos_alt

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
theorem _root_.solution (h1 : R1) (hb : BasisGeneral) : PowerSeriesFreeBasis := by
  intro l _ O _ _ h2 f
  obtain ⟨w, hw, -⟩ := h1 l O h2
  have h := hb O (l - 1) w (prime_sub_one_pos_alt l) f
  simpa only [inc, hw] using h
end Formalism.CohomologicalDescent.HeightDescentMinors
