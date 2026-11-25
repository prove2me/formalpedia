-- Prove2me | solution 1 for CompanionTheory.D.Upq.lieGroup_GL_complex_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:30.681702+00:00
-- url     : https://prove2.me/submissions/100b6e0b-6d17-4366-8a24-e0f394778c1a

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
theorem _root_.solution (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) k (GL (Fin n) ℂ) := inferInstance
end CompanionTheory.D.Upq
