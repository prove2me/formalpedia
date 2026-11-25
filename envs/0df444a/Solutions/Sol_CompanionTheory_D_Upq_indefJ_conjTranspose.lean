-- Prove2me | solution 1 for CompanionTheory.D.Upq.indefJ_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:12.003627+00:00
-- url     : https://prove2.me/submissions/3dd76ffd-ee2f-4ae8-9f2f-22d232bcc888

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
open Matrix
open scoped Matrix.Norms.L2Operator
variable (p q : ℕ)
namespace CompanionTheory.D.Upq
theorem _root_.solution : (indefJ p q)ᴴ = indefJ p q := by
  rw [indefJ, diagonal_conjTranspose]
  congr 1; funext i; cases i <;> simp
end CompanionTheory.D.Upq
