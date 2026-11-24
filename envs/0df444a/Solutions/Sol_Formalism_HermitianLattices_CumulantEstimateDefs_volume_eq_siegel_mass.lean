-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.volume_eq_siegel_mass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:35.239178+00:00
-- url     : https://prove2.me/submissions/65565c66-36e5-4da7-9080-18790ff6a2fc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_t2vol

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
theorem _root_.solution : VolumeDependsOnSumOfRecurrence := CumulantEstimates.t2vol
end Formalism.HermitianLattices.CumulantEstimateDefs
