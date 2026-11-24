-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.dsW_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:05:18.99983+00:00
-- url     : https://prove2.me/submissions/e61377aa-f4b0-4bf7-8672-e05add1d2ca4

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_add

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
theorem _root_.solution (h : RepOn G σ) {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v') :
    ∀ {W : List (Mat n)}, LieW G W → dsW σ W (v + v') = dsW σ W v + dsW σ W v'
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    simp only [dsW_cons]
    rw [solution h hv hv' hW', ds_add h (hW X List.mem_cons_self) (hv.dsW h hW') (hv'.dsW h hW')]
end CompanionTheory.D.Upq.Sm
