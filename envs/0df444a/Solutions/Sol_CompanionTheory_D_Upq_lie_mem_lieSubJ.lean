-- Prove2me | solution 1 for CompanionTheory.D.Upq.lie_mem_lieSubJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:35.923986+00:00
-- url     : https://prove2.me/submissions/b23071d0-ec71-4827-bde1-131b9f459b67

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
variable {J}
namespace CompanionTheory.D.Upq
theorem _root_.solution {X Y : Matrix n n ℂ} (hX : X ∈ lieSubJ J) (hY : Y ∈ lieSubJ J) :
    ⁅X, Y⁆ ∈ lieSubJ J :=
  (lieSubJ J).lie_mem hX hY
end CompanionTheory.D.Upq
