-- Prove2me | solution 1 for Formalism.REAL.positiveArraysInvariant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:30.945958+00:00
-- url     : https://prove2.me/submissions/3fdcec23-edfd-49b2-a959-9792fdb721d6

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_indexArrayAction_mul_permutePositions
import Theorems.Thm_Formalism_REAL_mem_symmetricArrays
import Theorems.Thm_Formalism_REAL_firstPositionSlice_positionAction_succ
import Theorems.Thm_Formalism_REAL_raisingPart_invariant
import Theorems.Thm_Formalism_REAL_admissibleArrays_invariant
import Theorems.Thm_Formalism_REAL_firstPositionSlice_indexArrayAction

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
theorem _root_.solution : NStable := by
  intro V _ _ n ε E Λ u j a b hab F hF
  simp only [Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hF ⊢
  obtain ⟨⟨h0, hs⟩, hv⟩ := hF
  refine ⟨⟨admissibleArrays_invariant ε E u (j+1) a b hab F h0, ?_⟩, fun α' => ?_⟩
  · rw [mem_symmetricArrays] at hs ⊢
    intro σ
    have h1 : arrE E (j+1) a b (permArr V n σ F) = permArr V n σ (arrE E (j+1) a b F) :=
      LinearMap.congr_fun (indexArrayAction_mul_permutePositions E σ a b) F
    rw [← h1, hs σ]
  · rw [firstPositionSlice_indexArrayAction]
    refine Submodule.add_mem _ (raisingPart_invariant ε E Λ u a b hab _ (hv α'))
      (Submodule.sum_mem _ fun k _ => ?_)
    rw [firstPositionSlice_positionAction_succ]
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;> first | exact hv _ | exact Submodule.zero_mem _
end Formalism.REAL
