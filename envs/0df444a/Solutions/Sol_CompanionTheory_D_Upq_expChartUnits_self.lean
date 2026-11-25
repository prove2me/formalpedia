-- Prove2me | solution 1 for CompanionTheory.D.Upq.expChartUnits_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:50.491378+00:00
-- url     : https://prove2.me/submissions/c9deba4c-3a84-4df9-9fae-07b5429d1e44

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Theorems.Thm_CompanionTheory_D_Upq_expPartialHomeomorph_symm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸
namespace CompanionTheory.D.Upq
theorem _root_.solution (g : 𝔸ˣ) : expChartUnits 𝕂 g g = 0 := by
  show (𝔢).symm ((g⁻¹ * g : 𝔸ˣ) : 𝔸) = 0
  simpa using expPartialHomeomorph_symm_one 𝕂 𝔸
end CompanionTheory.D.Upq
