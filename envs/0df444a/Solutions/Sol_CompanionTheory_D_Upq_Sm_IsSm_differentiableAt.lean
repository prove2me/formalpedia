-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:44.590301+00:00
-- url     : https://prove2.me/submissions/7eece98a-3d94-4a72-984d-b6017aef8ef9

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec

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
namespace IsSm
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) : DifferentiableAt ℝ (fun t => σ (ex X t) v) 0 :=
  (smOn_ds h (u := fun _ : ℝ => v) hv.prod hX).1 0 (mem_univ _)
end IsSm
end CompanionTheory.D.Upq.Sm
