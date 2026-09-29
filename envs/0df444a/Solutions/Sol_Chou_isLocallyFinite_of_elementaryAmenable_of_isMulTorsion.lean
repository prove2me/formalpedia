-- Prove2me | solution 1 for Chou.isLocallyFinite_of_elementaryAmenable_of_isMulTorsion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:58:40.155071+00:00
-- url     : https://prove2.me/submissions/3c250eef-3fce-4d32-afa4-074f9a3e9486

import Theorems.Thm_Chou_elementaryAmenable_iff_constructible
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-- `N ∩ B` inside `B` versus inside `N`. -/
def subgroupOfSwap {G : Type*} [Group G] (N B : Subgroup G) :
    ↥(N.subgroupOf B) ≃* ↥(B.subgroupOf N) where
  toFun x := ⟨⟨(x : B), x.2⟩, (x : B).2⟩
  invFun y := ⟨⟨(y : N), y.2⟩, (y : N).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The image of `B` in `G ⧸ M` is the quotient of `B` by `M ∩ B`. -/
noncomputable def quotientSubgroupOfEquivMap {G : Type*} [Group G] (B M : Subgroup G) [M.Normal] :
    B ⧸ M.subgroupOf B ≃* ↥(B.map (mk' M)) :=
  have h1 : M.subgroupOf B = ((mk' M).comp B.subtype).ker := by
    rw [← MonoidHom.comap_ker, ker_mk', comap_subtype]
  have h2 : ((mk' M).comp B.subtype).range = B.map (mk' M) := by
    rw [MonoidHom.range_comp, range_subtype]
  (quotientMulEquivOfEq h1).trans
    ((quotientKerEquivRange ((mk' M).comp B.subtype)).trans (MulEquiv.subgroupCongr h2))

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

lemma finite_map_of_finite {G H : Type*} [Group G] [Group H] (K : Subgroup G) [Finite K]
    (f : G →* H) : Finite (K.map f) := by
  have : Finite ↥(K : Set G) := ‹Finite ↥K›
  exact Set.finite_coe_iff.mpr (by rw [Subgroup.coe_map]; exact (Set.toFinite (K : Set G)).image f)

lemma subsingleton_of_iSup_empty {G : Type*} [Group G] {ι : Type*} [IsEmpty ι]
    (H : ι → Subgroup G) (hsup : ⨆ i, H i = ⊤) : Subsingleton G := by
  rw [iSup_of_empty] at hsup
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup G) := hsup ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup G) := hsup ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

lemma exists_subset_of_directed {G : Type*} [Group G] {ι : Type*} [Nonempty ι]
    {H : ι → Subgroup G} (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) {S : Set G}
    (hS : S.Finite) : ∃ k, S ⊆ H k := by
  classical
  obtain ⟨T, rfl⟩ := hS.exists_finset_coe
  clear hS
  induction T using Finset.induction_on with
  | empty => obtain ⟨k⟩ := ‹Nonempty ι›; exact ⟨k, by simp⟩
  | insert a T _ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj⟩ := (mem_iSup_of_directed hdir).mp (hsup ▸ mem_top a)
    obtain ⟨m, hkm, hjm⟩ := hdir k j
    refine ⟨m, ?_⟩
    rw [Finset.coe_insert]
    exact Set.insert_subset (hjm hj) (hk.trans hkm)

/-! ### Locally finite groups -/

lemma isLocallyFinite_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsLocallyFinite G) : IsLocallyFinite H := by
  intro S hS
  haveI := h _ (hS.image e.symm)
  have hcl : closure S = (closure (e.symm '' S)).map (e : G →* H) := by
    rw [MonoidHom.map_closure, Set.image_image]
    simp
  rw [hcl]
  exact finite_map_of_finite _ _

lemma isLocallyFinite_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsLocallyFinite N) (hQ : IsLocallyFinite (G ⧸ N)) : IsLocallyFinite G := by
  intro S hS
  haveI : Finite ↥S := hS.to_subtype
  haveI hHfg : Group.FG (closure S) := Group.closure_finite_fg S
  have himg : Finite ((closure S).map (mk' N)) := by
    rw [MonoidHom.map_closure]; exact hQ _ (hS.image _)
  haveI : Finite (closure S ⧸ N.subgroupOf (closure S)) :=
    Finite.of_equiv _ (quotientSubgroupOfEquivMap (closure S) N).symm.toEquiv
  haveI : (N.subgroupOf (closure S)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI hKfg : Group.FG (N.subgroupOf (closure S)) := inferInstance
  have e := subgroupOfSwap N (closure S)
  haveI : Group.FG ((closure S).subgroupOf N) :=
    Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨T, hT⟩ : ((closure S).subgroupOf N).FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  haveI : Finite ((closure S).subgroupOf N) := by
    have := hN (T : Set N) (Finset.finite_toSet T)
    rwa [hT] at this
  haveI : Finite (N.subgroupOf (closure S)) := Finite.of_equiv _ e.symm.toEquiv
  apply Nat.finite_of_card_ne_zero
  rw [← Subgroup.index_mul_card (N.subgroupOf (closure S))]
  exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Nat.card_pos.ne'

lemma isLocallyFinite_directedUnion {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) (h : ∀ i, IsLocallyFinite (H i)) :
    IsLocallyFinite G := by
  intro S hS
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := subsingleton_of_iSup_empty H hsup
    exact inferInstance
  · obtain ⟨k, hk⟩ := exists_subset_of_directed hdir hsup hS
    have hT : (Subtype.val ⁻¹' S : Set (H k)).Finite := hS.preimage Subtype.val_injective.injOn
    have hST : (H k).subtype '' (Subtype.val ⁻¹' S) = S :=
      Set.image_preimage_eq_of_subset (by rw [Subgroup.coe_subtype, Subtype.range_coe]; exact hk)
    haveI := h k _ hT
    rw [← hST, ← MonoidHom.map_closure]
    exact finite_map_of_finite _ _

theorem isLocallyFinite_of_constructible {G : Type u} [Group G] (hG : Constructible G) :
    IsMulTorsion G → IsLocallyFinite G := by
  induction hG with
  | @of_finite G _ _ => intro _ S _; exact inferInstance
  | @of_commGroup G _ =>
    intro ht S hS
    haveI : Finite ↥S := hS.to_subtype
    haveI : Group.FG (closure S) := Group.closure_finite_fg S
    exact CommGroup.finite_of_fg_isMulTorsion _ (ht.subgroup _)
  | @of_mulEquiv G H _ _ e _ ih =>
    intro ht
    exact isLocallyFinite_of_mulEquiv e
      (ih (IsMulTorsion.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective ht))
  | @extension G _ N _ _ _ ihN ihQ =>
    intro ht
    exact isLocallyFinite_extension N (ihN (ht.subgroup N))
      (ihQ (IsMulTorsion.of_surjective (mk'_surjective N) ht))
  | @directedUnion G _ ι H hdir hsup _ ih =>
    intro ht
    exact isLocallyFinite_directedUnion H hdir hsup (fun i => ih i (ht.subgroup (H i)))

/-- Theorem 2.3, first statement. -/
theorem isLocallyFinite_of_elementaryAmenable_of_isMulTorsion' {G : Type u} [Group G]
    (hG : ElementaryAmenable G) (ht : IsMulTorsion G) : IsLocallyFinite G :=
  isLocallyFinite_of_constructible (Chou.elementaryAmenable_iff_constructible.mp hG) ht

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

/-! ### Corollary 2.4 -/

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (hG : ElementaryAmenable G) (ht : IsMulTorsion G) :
    IsLocallyFinite G :=
  Chou.Lib.isLocallyFinite_of_elementaryAmenable_of_isMulTorsion' hG ht
