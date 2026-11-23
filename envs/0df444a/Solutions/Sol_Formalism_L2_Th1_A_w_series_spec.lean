-- Prove2me | solution 1 for Formalism.L2.Th1.A.w_series_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:59.552785+00:00
-- url     : https://prove2.me/submissions/a885eca3-77cc-4c40-8e4c-58f31cdef109

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_unique

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
open CurveSer
namespace Formalism.L2.Th1.A
theorem _root_.solution : WSerSpec.{u} := by
  unfold WSerSpec
  intro R _ W
  exact ⟨wSer_fixed W, fun w hw => wSer_unique W hw⟩
end Formalism.L2.Th1.A
