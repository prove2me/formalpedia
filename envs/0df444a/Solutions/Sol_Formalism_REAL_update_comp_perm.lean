-- Prove2me | solution 1 for Formalism.REAL.update_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:56.168294+00:00
-- url     : https://prove2.me/submissions/45748e1b-79fd-426d-875f-ef0ef2277221

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution {X : Type*} (σ : Equiv.Perm (Fin j)) (α : Fin j → X) (i : Fin j) (x : X) :
    (fun k => Function.update α i x (σ k)) = Function.update (fun k => α (σ k)) (σ.symm i) x := by
  funext k
  by_cases hk : k = σ.symm i
  · subst hk
    simp
  · have hk' : σ k ≠ i := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
    simp [Function.update_apply, hk, hk']
end Formalism.REAL
