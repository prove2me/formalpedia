-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.hyperbolic_sine_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:03.414959+00:00
-- url     : https://prove2.me/submissions/a2ebfc3d-d9cf-4d30-963d-3ec808e8f470

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_sinhAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs
namespace Formalism.HermitianLattices.CumulantEstimateDefs
theorem _root_.solution : SinhBounds := CumulantEstimates.sinhAll
end Formalism.HermitianLattices.CumulantEstimateDefs
