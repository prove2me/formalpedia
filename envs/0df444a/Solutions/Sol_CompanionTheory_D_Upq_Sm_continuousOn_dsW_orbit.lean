-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.continuousOn_dsW_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:21.41194+00:00
-- url     : https://prove2.me/submissions/6bcfadf5-6c2c-49b2-b908-8e09fa8a99f2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_continuousOn
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
theorem _root_.solution (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {W : List (Mat n)}
    (hW : LieW G W) : ContinuousOn (fun x => dsW σ W (σ x w)) G := by
  have h1 := SmOn.comp (smOn_dsW h (u := fun x => σ x w) (hw.smOn_mul h) hW)
    (φ := fun x : Mat n => ((1 : Mat n), x)) (B := G) (contDiff_const.prodMk contDiff_id)
    fun _ hg => ⟨h.one_mem, hg⟩
  refine h1.continuousOn.congr fun x _ => ?_
  simp [h.map_one]
end CompanionTheory.D.Upq.Sm
