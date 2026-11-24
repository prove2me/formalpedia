-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.height_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:11.3428+00:00
-- url     : https://prove2.me/submissions/bce82b61-9a1f-471e-8f8f-83e71eab5252

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_yBound

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
theorem _root_.solution : EigenvalueSumBound := CumulantEstimates.yBound
end Formalism.HermitianLattices.CumulantEstimateDefs
