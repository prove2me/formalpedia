-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.cumulant_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:46.395662+00:00
-- url     : https://prove2.me/submissions/c22868af-f302-4db8-9be0-e461866009c2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_cumU

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
theorem _root_.solution : CumulantUpperBound := CumulantEstimates.cumU
end Formalism.HermitianLattices.CumulantEstimateDefs
