-- Prove2me | solution 1 for Formalism.REAL.mixedCasimir_mul_permuteFactors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:58:59.886405+00:00
-- url     : https://prove2.me/submissions/830740e1-ba38-4666-9042-ba131af81b71

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_mul_permuteFactors
import Theorems.Thm_Formalism_REAL_pointwiseAction_mul_permutePositions

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j))
    (i : Fin j) : OmS ε E i * permArr V n σ = permArr V n σ * OmS ε E (σ.symm i) := by
  simp only [OmS, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · rw [mul_assoc, pointwiseAction_mul_permutePositions, ← mul_assoc, factorAction_mul_permuteFactors, mul_assoc]
  · simp
end Formalism.REAL
