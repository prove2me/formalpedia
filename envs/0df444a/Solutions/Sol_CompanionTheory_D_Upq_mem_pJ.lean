-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_pJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:24.339198+00:00
-- url     : https://prove2.me/submissions/7bfe6604-7017-4753-8cbb-bced44f781e7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)
namespace CompanionTheory.D.Upq
theorem _root_.solution {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ X * J = -(J * X) := Iff.rfl
end CompanionTheory.D.Upq
