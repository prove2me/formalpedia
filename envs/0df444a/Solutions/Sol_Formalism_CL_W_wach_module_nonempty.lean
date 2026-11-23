-- Prove2me | solution 1 for Formalism.CL.W.wach_module_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.216413+00:00
-- url     : https://prove2.me/submissions/3ae8e64d-de75-4636-925f-58773e8273b1

import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
import Theorems.Thm_Formalism_CL_W_polyW_nondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CL Formalism.CL.W
namespace Formalism.CL.W
theorem _root_.solution : WachNonempty := fun p _ => ⟨polyW p, polyW_nondeg p⟩
end Formalism.CL.W
