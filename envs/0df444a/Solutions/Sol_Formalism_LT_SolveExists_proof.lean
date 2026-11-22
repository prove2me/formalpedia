-- Prove2me | solution 1 for Formalism.LT.SolveExists_proof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:10.398799+00:00
-- url     : https://prove2.me/submissions/57c43970-f811-4702-8735-44398c91e02c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SolveExistsProof
import Theorems.Thm_Formalism_LT_SolveP_SolveExists_proof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
namespace Formalism.LT
theorem _root_.solution : Formalism.LT.SolveExists.{u, v} := Formalism.LT.SolveP.SolveExists_proof
end Formalism.LT
