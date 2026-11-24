-- Prove2me | solution 1 for Formalism.SL.Final.eichInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:11.068515+00:00
-- url     : https://prove2.me/submissions/6b321717-8d1e-43c0-b53b-2d3b092897b1

import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_EichlerEquivalenceHolds
import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementCS
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_LfProd
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementMV
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementNC
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Theorems.Thm_Formalism_SL_P_eichler_inverse_holds


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
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichInv := Formalism.SL.P.eichler_inverse_holds
end Formalism.SL.Final
