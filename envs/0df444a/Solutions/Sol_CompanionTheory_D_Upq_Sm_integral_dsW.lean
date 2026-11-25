-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.integral_dsW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:52.320865+00:00
-- url     : https://prove2.me/submissions/ddd9e613-0f81-405c-b12b-39b1edcc0e4b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_contDiff_LW
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasCompactSupport_LW
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_A
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_B

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
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {φ : Mat n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ∀ {W : List (Mat n)}, LieW G W →
    ∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar =
      ∫ g : MG G hG, LW W φ g.mat • σ g.mat v ∂haar
  | [], _ => rfl
  | X :: W, hXW => by
    have hW : LieW G W := fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)
    have hX := hXW X List.mem_cons_self
    have h1 := hasDerivAt_B (hG := hG) h hv hX hW hφ.continuous hc
    rw [solution h hv hφ hc hW] at h1
    exact h1.unique (hasDerivAt_A h hv hX (contDiff_LW hφ W) (hasCompactSupport_LW hc W))
end CompanionTheory.D.Upq.Sm
