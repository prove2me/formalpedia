-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_le_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:26.814857+00:00
-- url     : https://prove2.me/submissions/8015d013-ee73-4232-b2d4-7196aeef1e66

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
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
theorem _root_.solution {β γ : Type*} (m : Multiset β) (f : β → γ) (s : Multiset γ)
    (h : s ≤ m.map f) : ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on generalizing s with
  | empty =>
    simp only [Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨0, le_rfl, by simp [h]⟩
  | cons b m ih =>
    rw [Multiset.map_cons] at h
    by_cases hb : f b ∈ s
    · have hs := Multiset.cons_erase hb
      rw [← hs, Multiset.cons_le_cons_iff] at h
      obtain ⟨t, ht, htm⟩ := ih _ h
      exact ⟨b ::ₘ t, Multiset.cons_le_cons _ ht, by rw [Multiset.map_cons, htm, hs]⟩
    · rw [Multiset.le_cons_of_notMem hb] at h
      obtain ⟨t, ht, htm⟩ := ih _ h
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htm⟩
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
