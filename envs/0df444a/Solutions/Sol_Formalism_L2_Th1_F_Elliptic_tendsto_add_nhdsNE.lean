-- Prove2me | solution 1 for Formalism.L2.Th1.F.Elliptic.tendsto_add_nhdsNE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:04.487365+00:00
-- url     : https://prove2.me/submissions/bd4de611-a7c2-4cd7-95dc-b95fb3ff82f3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Elliptic
namespace Formalism.L2.Th1.F.Elliptic
theorem _root_.solution (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_right ω).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw (add_right_cancel h)
end Formalism.L2.Th1.F.Elliptic
