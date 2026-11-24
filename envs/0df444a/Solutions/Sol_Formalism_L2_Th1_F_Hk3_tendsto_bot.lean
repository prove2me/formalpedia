-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.tendsto_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:15.003911+00:00
-- url     : https://prove2.me/submissions/57f7d399-a9dd-41f3-94dd-2b52a1be3d8b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_tendsto_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution : Tendsto (fun t : ℝ => 1 + t ^ 2) atBot atTop := by
  have := tendsto_top.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this
end Formalism.L2.Th1.F.Hk3
