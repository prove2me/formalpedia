-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.minors_dvd_mul_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:01.171348+00:00
-- url     : https://prove2.me/submissions/8dc051e0-7043-4ce2-aae8-3ad1a69b3d98

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_mul_left
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_mul_right
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_of_minorsDvd

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
theorem _root_.solution : MinorsDvdMul := by
  intro R _ m n p r t x G P H h f g _ _
  exact dvd_det_submatrix_mul_right x (G * P) H (dvd_det_submatrix_mul_left x G P (dvd_det_submatrix_of_minorsDvd x P h)) f g
end Formalism.CohomologicalDescent.HeightDescentMinors
