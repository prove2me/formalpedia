-- Prove2me | solution 1 for Formalism.SL.Final.primesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:32.133408+00:00
-- url     : https://prove2.me/submissions/ee4a7c02-0f23-4e3a-aa7c-f3a8bd4e2ce4

import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_EichlerEquivalenceHolds
import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementCS
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_LfProd
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementMV
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementNC
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Theorems.Thm_Formalism_SL_P_primes_over_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SL Formalism.SL.Final
namespace Formalism.SL.Final
theorem _root_.solution : Formalism.SL.LF.PrimesOver := Formalism.SL.P.primes_over_holds
end Formalism.SL.Final
