-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.map_logSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:09.386234+00:00
-- url     : https://prove2.me/submissions/d5719221-996e-43ca-b94e-8928b750f9dc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_More_map_integ
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_om


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (W : WeierstrassCurve K) :
    PowerSeries.map φ (logSer W) = logSer (W.map φ) := by
  rw [logSer, map_integ, CurveSer.map_om, logSer]
end Formalism.L2.Th1.A.More
