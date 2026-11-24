-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.dsW_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:32.61328+00:00
-- url     : https://prove2.me/submissions/faf04b29-1aa3-4f2c-8fc2-b365e8987d28

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul

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
theorem _root_.solution (h : RepOn G σ) {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v')
    {W : List (Mat n)} (hW : LieW G W) : dsW σ W (v - v') = dsW σ W v - dsW σ W v' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v', dsW_add h hv (hv'.smul _) hW, dsW_smul h hv' _ hW,
    neg_one_smul, ← sub_eq_add_neg]
end CompanionTheory.D.Upq.Sm
