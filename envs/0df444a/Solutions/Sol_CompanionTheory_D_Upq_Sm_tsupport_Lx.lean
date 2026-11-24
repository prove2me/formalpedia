-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.tsupport_Lx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:59.243294+00:00
-- url     : https://prove2.me/submissions/3b1f4671-aff1-443e-b907-c9cb4a243d69

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed

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
theorem _root_.solution (X : Mat n) (φ : Mat n → ℝ) : tsupport (Lx X φ) ⊆ tsupport φ := by
  refine (closure_mono fun g hg => ?_).trans (tsupport_fderiv_subset ℝ (f := φ))
  intro h
  exact hg (by simp [Lx, h])
end CompanionTheory.D.Upq.Sm
