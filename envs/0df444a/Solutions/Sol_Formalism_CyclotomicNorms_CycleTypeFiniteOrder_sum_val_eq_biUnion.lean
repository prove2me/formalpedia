-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.sum_val_eq_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.257631+00:00
-- url     : https://prove2.me/submissions/b624b8b8-bf00-47e7-bedf-7a69699055c6

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (I : Finset (Finset K))
    (hI : ∀ S ∈ I, ∀ T ∈ I, S ≠ T → Disjoint S T) :
    ∑ S ∈ I, S.val = (I.biUnion id).val := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert S I hSI ih =>
    rw [Finset.sum_insert hSI, ih (fun A hA B hB h => hI A (Finset.mem_insert_of_mem hA) B
      (Finset.mem_insert_of_mem hB) h), Finset.biUnion_insert]
    have hd : Disjoint S (I.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro T hT
      exact hI S (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hT)
        (fun h => hSI (h ▸ hT))
    change S.val + _ = (S ∪ _).val
    rw [← Finset.disjUnion_eq_union _ _ hd]
    rfl
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
