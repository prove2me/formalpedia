-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.dsW_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:05:33.288906+00:00
-- url     : https://prove2.me/submissions/cd4903c8-7aec-4c71-a9fb-cac9051ade8b

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_smul

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
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (c : ℂ) :
    ∀ {W : List (Mat n)}, LieW G W → dsW σ W (c • v) = c • dsW σ W v
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    simp only [dsW_cons]
    rw [solution h hv c hW', ds_smul h (hW X List.mem_cons_self) (hv.dsW h hW')]
end CompanionTheory.D.Upq.Sm
