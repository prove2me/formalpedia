-- Prove2me | solution 1 for CompanionTheory.D.Upq.expChart_GL_mem_maximalAtlas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:26.651343+00:00
-- url     : https://prove2.me/submissions/c228f643-6c88-48d1-9138-948718aec1da

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Theorems.Thm_CompanionTheory_D_Upq_expChartUnits_mem_maximalAtlas

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
theorem _root_.solution (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (g : GL (Fin n) 𝕂)
    (k : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) :=
  expChartUnits_mem_maximalAtlas 𝕂 g k
end CompanionTheory.D.Upq
