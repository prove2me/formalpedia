-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasCompactSupport_LW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:56.325218+00:00
-- url     : https://prove2.me/submissions/526e834e-b551-4ec1-9f7b-253d4e387d0e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_tsupport_LW

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
theorem _root_.solution {φ : Mat n → ℝ} (hc : HasCompactSupport φ) (W : List (Mat n)) :
    HasCompactSupport (LW W φ) :=
  IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_LW φ W)
end CompanionTheory.D.Upq.Sm
