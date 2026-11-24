-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.apply_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:18.163701+00:00
-- url     : https://prove2.me/submissions/e1ad6dd1-84ef-4e16-8271-3208e0e9c7b3

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integrable_smul

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
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
variable [CompleteSpace H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (L : H →L[ℂ] H) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {f : MG G hG → H} (hf : Continuous f) :
    L (∫ g : MG G hG, φ g.mat • f g ∂haar) = ∫ g : MG G hG, φ g.mat • L (f g) ∂haar := by
  rw [← L.integral_comp_comm (integrable_smul hφ hc hf)]
  simp only [ContinuousLinearMap.map_smul_of_tower]
end CompanionTheory.D.Upq.Sm
