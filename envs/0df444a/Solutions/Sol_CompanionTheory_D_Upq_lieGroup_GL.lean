-- Prove2me | solution 1 for CompanionTheory.D.Upq.lieGroup_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:47.326273+00:00
-- url     : https://prove2.me/submissions/ceee366f-bb15-42d4-9219-e5041c509ce8

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
open scoped Matrix.Norms.L2Operator
namespace CompanionTheory.D.Upq
theorem _root_.solution (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := inferInstance
end CompanionTheory.D.Upq
