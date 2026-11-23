-- Prove2me | solution 1 for CompanionTheory.D.Upq.expPartialHomeomorph_symm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:12.825653+00:00
-- url     : https://prove2.me/submissions/f44b0ca4-6493-4f22-8ae0-c5a74a5578cc

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
variable (𝕂 : Type*) [RCLike 𝕂] (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
namespace CompanionTheory.D.Upq
theorem _root_.solution : (expPartialHomeomorph 𝕂 𝔸).symm 1 = 0 := by
  simpa [coe_expPartialHomeomorph] using
    (expPartialHomeomorph 𝕂 𝔸).left_inv (zero_mem_expPartialHomeomorph_source 𝕂 𝔸)
end CompanionTheory.D.Upq
