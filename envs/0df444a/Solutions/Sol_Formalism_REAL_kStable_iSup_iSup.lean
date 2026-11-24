-- Prove2me | solution 1 for Formalism.REAL.kStable_iSup_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:57.044943+00:00
-- url     : https://prove2.me/submissions/27936d5a-b38f-47a1-8935-6c6a12e68020

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
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] (ε : Fin n → Bool)
    (T : Fin n → Fin n → Module.End ℂ W) {ι : Type*} {κ : ι → Prop} (S : ∀ i, κ i → Submodule ℂ W)
    (h : ∀ i k, KStable ε T (S i k)) : KStable ε T (⨆ i, ⨆ k, S i k) := by
  intro a b hab x hx
  have hle : (⨆ i, ⨆ k, S i k) ≤ Submodule.comap (T a b) (⨆ i, ⨆ k, S i k) := by
    refine iSup_le fun i => iSup_le fun k => ?_
    intro y hy
    exact (le_iSup_of_le i (le_iSup_of_le k le_rfl) : S i k ≤ ⨆ i, ⨆ k, S i k) (h i k a b hab y hy)
  exact hle hx
end Formalism.REAL
