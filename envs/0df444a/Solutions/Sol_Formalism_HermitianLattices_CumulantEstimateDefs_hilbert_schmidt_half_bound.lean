-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.hilbert_schmidt_half_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:39.119065+00:00
-- url     : https://prove2.me/submissions/15c2ddbc-dab4-4262-921e-ce6c482dc6bf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_hsHalf

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
theorem _root_.solution : HilbertSchmidtHalfBound := CumulantEstimates.hsHalf
end Formalism.HermitianLattices.CumulantEstimateDefs
