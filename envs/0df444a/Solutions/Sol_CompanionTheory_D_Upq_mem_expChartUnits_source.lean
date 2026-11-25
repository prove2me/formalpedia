-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_expChartUnits_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:39.483587+00:00
-- url     : https://prove2.me/submissions/3500dc49-a52c-4260-892d-19f101e34b36

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm

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
theorem _root_.solution (g : 𝔸ˣ) : g ∈ (expChartUnits 𝕂 g).source := by
  show ((g⁻¹ * g : 𝔸ˣ) : 𝔸) ∈ (𝔢).target
  simpa using one_mem_expPartialHomeomorph_target 𝕂 𝔸
end CompanionTheory.D.Upq
