-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:17.300859+00:00
-- url     : https://prove2.me/submissions/9f3008c1-c256-4065-a9b3-eeb070f96e32

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smOn_mul

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
theorem _root_.solution (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {x : Mat n} (hx : x ∈ G) :
    IsSm G σ (σ x w) :=
  SmOn.comp (hw.smOn_mul h) (φ := fun g : Mat n => (g, x)) (contDiff_id.prodMk contDiff_const)
    fun _ hg => ⟨hg, hx⟩
end IsSm
end CompanionTheory.D.Upq.Sm
