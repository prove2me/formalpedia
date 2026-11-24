-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.contDiff_Lx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:54.81773+00:00
-- url     : https://prove2.me/submissions/1787b721-5393-4211-8a35-4cada5a13952

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
theorem _root_.solution (X : Mat n) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Lx X φ) :=
  ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul' contDiff_const contDiff_id)).neg
end CompanionTheory.D.Upq.Sm
