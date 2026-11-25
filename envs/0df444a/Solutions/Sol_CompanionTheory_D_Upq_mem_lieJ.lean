-- Prove2me | solution 1 for CompanionTheory.D.Upq.mem_lieJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:21.195373+00:00
-- url     : https://prove2.me/submissions/7cbfff55-98bb-420e-b7b9-bb42e8a1aca2

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
theorem _root_.solution {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ * J + J * X = 0 := Iff.rfl
end CompanionTheory.D.Upq
