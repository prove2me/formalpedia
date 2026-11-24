-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.ds_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:48:37.456605+00:00
-- url     : https://prove2.me/submissions/c3ed2532-fe80-49da-b23e-f77745489de7

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {v v' : H} (hv : IsSm G σ v)
    (hv' : IsSm G σ v') : ds σ X (v + v') = ds σ X v + ds σ X v' := by
  unfold ds
  simp only [map_add]
  exact deriv_fun_add (hv.differentiableAt h hX) (hv'.differentiableAt h hX)
end CompanionTheory.D.Upq.Sm
