-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.linear_extension_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:01.240976+00:00
-- url     : https://prove2.me/submissions/e68a5e99-51f1-47bf-a99b-e04c5b5e66cb

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_LinearExtensionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution : ExtendLin := by
  intro k _ M T _ _ _ _ ι f g hfg
  classical
  let φ := Finsupp.linearCombination k f
  let ψ := Finsupp.linearCombination k g
  have hle : LinearMap.ker φ ≤ LinearMap.ker ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    simp only [φ, ψ, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    exact hfg c.support c hc
  let φ' := (LinearMap.ker φ).liftQ φ le_rfl
  let ψ' := (LinearMap.ker φ).liftQ ψ hle
  have hinj : LinearMap.ker φ' = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    exact le_rfl
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ' hinj
  refine ⟨ψ'.comp L, fun i => ?_⟩
  have hfi : f i = φ' (Submodule.Quotient.mk (Finsupp.single i 1)) := by
    simp [φ', φ, Finsupp.linearCombination_single]
  have h2 : L (φ' (Submodule.Quotient.mk (Finsupp.single i 1))) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  rw [LinearMap.comp_apply, hfi, h2]
  simp [ψ', ψ, Finsupp.linearCombination_single]
end Formalism.L2.PairingIndexBounds.Mv
