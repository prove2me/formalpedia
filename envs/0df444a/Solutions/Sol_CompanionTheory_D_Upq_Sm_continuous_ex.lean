-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.continuous_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:49.898411+00:00
-- url     : https://prove2.me/submissions/6eae5eca-cabb-4e1f-a655-36eba1416421

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (X : Mat n) : Continuous (ex X) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ex X t).continuousAt
end CompanionTheory.D.Upq.Sm
