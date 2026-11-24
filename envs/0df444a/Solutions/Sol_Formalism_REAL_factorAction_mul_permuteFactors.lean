-- Prove2me | solution 1 for Formalism.REAL.factorAction_mul_permuteFactors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:06.279444+00:00
-- url     : https://prove2.me/submissions/7c149f05-f691-4253-a8ce-0728a3815cd5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArray_ext
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_permutePositions_apply
import Theorems.Thm_Formalism_REAL_update_comp_perm

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
theorem _root_.solution (σ : Equiv.Perm (Fin j)) (i : Fin j) (c d : Fin n) :
    factorAction (V := V) i c d * permArr V n σ = permArr V n σ * factorAction (σ.symm i) c d := by
  refine LinearMap.ext fun F => indexArray_ext fun α => ?_
  change factorAction i c d (permArr V n σ F) α = permArr V n σ (factorAction (σ.symm i) c d F) α
  simp only [factorAction_apply, permutePositions_apply, update_comp_perm, Equiv.apply_symm_apply]
end Formalism.REAL
