-- Prove2me | solution 1 for Formalism.SLP.P.CountO.mul_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:25.421643+00:00
-- url     : https://prove2.me/submissions/937159c1-b44f-4d32-8498-2996c14f3cb3

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_index_sup_mulSub_dvd
import Theorems.Thm_Formalism_SLP_P_CountO_inf_sup_mulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.SLP.P.CountO
theorem _root_.solution {a b : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (h1 : (idxSet R X a).Finite) (h2 : (idxSet R X b).Finite) :
    (idxSet R X (a * b)).Finite ∧
      (idxSet R X (a * b)).ncard ≤ (idxSet R X a).ncard * (idxSet R X b).ncard := by
  let F : Submodule R X → Submodule R X × Submodule R X :=
    fun N => (N ⊔ mulSub R X a, N ⊔ mulSub R X b)
  have hmaps : ∀ N ∈ idxSet R X (a * b), F N ∈ idxSet R X a ×ˢ idxSet R X b := by
    intro N hN
    have hN' : N.toAddSubgroup.index = a * b := hN
    have d1 := index_sup_mulSub_dvd N hab ha hb hN'
    have d2 := index_sup_mulSub_dvd N hab.symm hb ha (by rw [hN', mul_comm])
    have hinf := inf_sup_mulSub N hab hN'
    have hle : a * b ≤ (N ⊔ mulSub R X a).toAddSubgroup.index *
        (N ⊔ mulSub R X b).toAddSubgroup.index := by
      rw [← hN']
      conv_lhs => rw [← hinf]
      exact AddSubgroup.index_inf_le (H := (N ⊔ mulSub R X a).toAddSubgroup)
        (K := (N ⊔ mulSub R X b).toAddSubgroup)
    set i1 := (N ⊔ mulSub R X a).toAddSubgroup.index
    set i2 := (N ⊔ mulSub R X b).toAddSubgroup.index
    have l1 : i1 ≤ a := Nat.le_of_dvd ha d1
    have l2 : i2 ≤ b := Nat.le_of_dvd hb d2
    have e1 : i1 = a := by
      refine le_antisymm l1 ?_
      have : a * b ≤ i1 * b := hle.trans (Nat.mul_le_mul_left _ l2)
      exact Nat.le_of_mul_le_mul_right this hb
    have e2 : i2 = b := by
      refine le_antisymm l2 ?_
      have : a * b ≤ a * i2 := hle.trans (Nat.mul_le_mul_right _ l1)
      exact Nat.le_of_mul_le_mul_left this ha
    exact ⟨e1, e2⟩
  have hinj : Set.InjOn F (idxSet R X (a * b)) := by
    intro N₁ h₁ N₂ h₂ h
    simp only [F, Prod.mk.injEq] at h
    rw [← inf_sup_mulSub N₁ hab h₁, ← inf_sup_mulSub N₂ hab h₂, h.1, h.2]
  refine ⟨Set.Finite.of_finite_image ((h1.prod h2).subset (Set.image_subset_iff.mpr hmaps)) hinj,
    ?_⟩
  rw [← Set.ncard_prod]
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (h1.prod h2)
end Formalism.SLP.P.CountO
