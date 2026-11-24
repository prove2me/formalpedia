-- Prove2me | solution 1 for Formalism.GM.projectorIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.529228+00:00
-- url     : https://prove2.me/submissions/124e3fd1-ecc2-46ee-8cec-8949f5439daa

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_phi_integrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.PhiInt := M.PhiIntegrality.phi_integrality
end Formalism.GM
