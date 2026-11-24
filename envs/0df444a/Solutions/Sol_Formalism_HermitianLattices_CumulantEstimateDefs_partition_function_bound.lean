-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.partition_function_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:11.487121+00:00
-- url     : https://prove2.me/submissions/d3c5526a-5b25-47aa-a2f8-7012f145943e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_zBound

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
theorem _root_.solution : PartitionFunctionBound := CumulantEstimates.zBound
end Formalism.HermitianLattices.CumulantEstimateDefs
