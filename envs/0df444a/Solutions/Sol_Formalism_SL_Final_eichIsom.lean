-- Prove2me | solution 1 for Formalism.SL.Final.eichIsom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:34.983148+00:00
-- url     : https://prove2.me/submissions/87e0437a-51ff-4025-bc21-e18bfa404e41

import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_EichlerEquivalenceHolds
import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementCS
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_LfProd
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementMV
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementNC
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Theorems.Thm_Formalism_SL_P_eichler_isometry_holds


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
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichIsom := Formalism.SL.P.eichler_isometry_holds
end Formalism.SL.Final
