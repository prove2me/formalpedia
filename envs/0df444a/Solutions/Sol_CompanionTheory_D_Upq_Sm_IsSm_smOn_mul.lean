-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.smOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:30.179172+00:00
-- url     : https://prove2.me/submissions/5c73c67d-b7d0-4fe5-acc9-ce9eddbddbc3

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
theorem _root_.solution (h : RepOn G σ) {w : H} (hw : IsSm G σ w) :
    SmOn (G ×ˢ G) (fun q : Mat n × Mat n => σ q.1 (σ q.2 w)) :=
  (SmOn.comp hw contDiff_mul fun _ hq => h.mul_mem _ hq.1 _ hq.2).congr
    fun _ hq => (h.apply_mul hq.1 hq.2 w).symm
end IsSm
end CompanionTheory.D.Upq.Sm
