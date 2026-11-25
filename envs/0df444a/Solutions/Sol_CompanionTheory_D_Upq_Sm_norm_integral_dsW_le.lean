-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.norm_integral_dsW_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:19.38879+00:00
-- url     : https://prove2.me/submissions/ea581534-b3a0-4316-b0d3-5a5c7e9947b5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integral_dsW

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
theorem _root_.solution (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {W : List (Mat n)} (hW : LieW G W) :
    ‖∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar‖ ≤
      (∫ g : MG G hG, ‖LW W φ g.mat‖ ∂haar) * ‖v‖ := by
  rw [integral_dsW h hv hφ hc hW, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  ext1 g
  rw [norm_smul, hiso _ g.mem]
end CompanionTheory.D.Upq.Sm
