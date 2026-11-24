-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.ds_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:48:38.276413+00:00
-- url     : https://prove2.me/submissions/8bc5d5dc-8368-42b4-af21-4080ad401471

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
theorem _root_.solution (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v)
    (c : ℂ) : ds σ X (c • v) = c • ds σ X v := by
  unfold ds
  simp only [map_smul]
  exact deriv_fun_const_smul c (hv.differentiableAt h hX)
end CompanionTheory.D.Upq.Sm
