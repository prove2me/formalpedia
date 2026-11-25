-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.coset_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:00.060788+00:00
-- url     : https://prove2.me/submissions/f7c680c5-6406-4a96-aaea-ae5bcb5ca4a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IdealCovol
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (L Λ : AddSubgroup V)
    (hle : Λ ≤ L) (hfin : (Λ.addSubgroupOf L).FiniteIndex) (FL : Set V) (hFL : MeasurableSet FL)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) :
    ∃ G : Set V, MeasurableSet G ∧ ∀ v, ∃! a : Λ, (a : V) + v ∈ G := by
  set Λ' := Λ.addSubgroupOf L
  have : Finite (L ⧸ Λ') := Λ'.finite_quotient_of_finiteIndex
  have : Fintype (L ⧸ Λ') := Fintype.ofFinite _
  let rep : L ⧸ Λ' → L := fun q => q.out
  let G : Set V := ⋃ q : L ⧸ Λ', (fun y => ((rep q : L) : V) + y) ⁻¹' FL
  refine ⟨G, MeasurableSet.iUnion fun q => measurable_const_add _ hFL, fun v => ?_⟩
  obtain ⟨l, hl, hlu⟩ := hdL v
  set q : L ⧸ Λ' := (l : L ⧸ Λ')
  have hdiff : -(rep q) + l ∈ Λ' := by
    have : ((rep q : L) : L ⧸ Λ') = q := QuotientAddGroup.out_eq' q
    rw [← QuotientAddGroup.eq]; exact this
  have hΛ : ((-(rep q) + l : L) : V) ∈ Λ := by
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff; exact hdiff
  refine ⟨⟨_, hΛ⟩, Set.mem_iUnion.2 ⟨q, ?_⟩, ?_⟩
  · show ((rep q : L) : V) + (((-(rep q) + l : L) : V) + v) ∈ FL
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← add_assoc, add_neg_cancel_left]; exact hl
  · rintro ⟨a, ha⟩ haG
    obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 haG
    have hq'' : ((rep q' : L) : V) + (a + v) ∈ FL := hq'
    have hmem : ((rep q' : V) + a) ∈ L := L.add_mem (rep q').2 (hle ha)
    have h1 : (⟨(rep q' : V) + a, hmem⟩ : L) = l := hlu _ (by show (rep q' : V) + a + v ∈ FL; rw [add_assoc]; exact hq'')

    have hqq : q' = q := by
      have e : (rep q' : L) + ⟨a, hle ha⟩ = l := by
        apply Subtype.ext; simpa using congrArg Subtype.val h1
      have hmk : ((l : L) : L ⧸ Λ') = ((rep q' : L) : L ⧸ Λ') := by
        rw [← e, QuotientAddGroup.eq]
        simp only [neg_add_rev, neg_add_cancel_right]
        rw [AddSubgroup.mem_addSubgroupOf]
        simpa using Λ.neg_mem ha
      rw [show ((rep q' : L) : L ⧸ Λ') = q' from QuotientAddGroup.out_eq' q'] at hmk
      exact hmk.symm
    apply Subtype.ext
    show a = ((-(rep q) + l : L) : V)
    have := congrArg Subtype.val h1
    simp only at this
    rw [← hqq]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← this]
    abel
end Formalism.L2.SG.NGCut.SplitEmbedding
