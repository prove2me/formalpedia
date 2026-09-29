-- Prove2me | solution 1 for Chou.exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T12:13:17.516254+00:00
-- url     : https://prove2.me/submissions/6cb5c738-9299-4855-a278-2ed4418a4cd8

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib
import Theorems.Thm_CannonFloydParry_not_elementaryAmenable_F
import Theorems.Thm_CannonFloydParry_no_free_subgroup_of_rank_two

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

/-- Proposition 2.1: the constructible groups are closed under subgroups and quotients. -/
theorem constructible_closed {G : Type u} [Group G] (h : Constructible G) :
    (∀ B : Subgroup G, Constructible B) ∧
      (∀ (M : Subgroup G) [M.Normal], Constructible (G ⧸ M)) := by
  induction h with
  | @of_finite G _ _ =>
    exact ⟨fun B => .of_finite B, fun M _ => .of_finite (G ⧸ M)⟩
  | @of_commGroup G _ =>
    exact ⟨fun B => .of_commGroup B, fun M _ => .of_commGroup (G ⧸ M)⟩
  | @of_mulEquiv G H _ _ e _ ih =>
    refine ⟨fun B => ?_, fun M _ => ?_⟩
    · have hK : (B.comap (e : G →* H)).map (e : G →* H) = B :=
        map_comap_eq_self_of_surjective e.surjective B
      exact .of_mulEquiv ((e.subgroupMap (B.comap (e : G →* H))).trans
        (MulEquiv.subgroupCongr hK)) (ih.1 _)
    · have : (M.comap (e : G →* H)).Normal := ‹M.Normal›.comap _
      have hm : (M.comap (e : G →* H)).map (e : G →* H) = M :=
        map_comap_eq_self_of_surjective e.surjective M
      exact .of_mulEquiv (QuotientGroup.congr _ _ e hm) (ih.2 _)
  | @extension G _ N _ _ _ ihN ihQ =>
    refine ⟨fun B => ?_, fun M _ => ?_⟩
    · refine Constructible.extension (N.subgroupOf B) ?_ ?_
      · exact .of_mulEquiv (subgroupOfSwap N B).symm (ihN.1 _)
      · exact .of_mulEquiv (quotientSubgroupOfEquivMap B N).symm (ihQ.1 _)
    · have : (N.map (mk' M)).Normal := ‹N.Normal›.map _ (mk'_surjective M)
      refine Constructible.extension (N.map (mk' M)) ?_ ?_
      · exact .of_mulEquiv (quotientSubgroupOfEquivMap N M) (ihN.2 (M.subgroupOf N))
      · have hEq : N.map (mk' M) = (N ⊔ M).map (mk' M) := by
          rw [Subgroup.map_sup, map_mk'_self, sup_bot_eq]
        have e₁ : (G ⧸ M) ⧸ N.map (mk' M) ≃* G ⧸ (N ⊔ M) :=
          (quotientMulEquivOfEq hEq).trans (quotientQuotientEquivQuotient M (N ⊔ M) le_sup_right)
        have e₂ : G ⧸ (N ⊔ M) ≃* (G ⧸ N) ⧸ (N ⊔ M).map (mk' N) :=
          (quotientQuotientEquivQuotient N (N ⊔ M) le_sup_left).symm
        exact .of_mulEquiv (e₁.trans e₂).symm (ihQ.2 ((N ⊔ M).map (mk' N)))
  | @directedUnion G _ ι H hdir hsup _ ih =>
    refine ⟨fun B => ?_, fun M _ => ?_⟩
    · rcases isEmpty_or_nonempty ι with hι | hι
      · have hsub : Subsingleton G := by
          rw [iSup_of_empty] at hsup
          refine ⟨fun a b => ?_⟩
          have ha : a ∈ (⊥ : Subgroup G) := hsup ▸ mem_top a
          have hb : b ∈ (⊥ : Subgroup G) := hsup ▸ mem_top b
          rw [mem_bot] at ha hb
          rw [ha, hb]
        exact .of_finite B
      · refine Constructible.directedUnion (fun i => (H i).subgroupOf B) ?_ ?_ ?_
        · intro i j
          obtain ⟨k, hik, hjk⟩ := hdir i j
          exact ⟨k, fun x hx => hik hx, fun x hx => hjk hx⟩
        · rw [eq_top_iff]
          intro x _
          obtain ⟨i, hi⟩ := (mem_iSup_of_directed hdir).mp (hsup ▸ mem_top (x : G))
          exact mem_iSup_of_mem i hi
        · intro i
          exact .of_mulEquiv (subgroupOfSwap (H i) B).symm ((ih i).1 _)
    · refine Constructible.directedUnion (fun i => (H i).map (mk' M)) ?_ ?_ ?_
      · intro i j
        obtain ⟨k, hik, hjk⟩ := hdir i j
        exact ⟨k, map_mono hik, map_mono hjk⟩
      · rw [← Subgroup.map_iSup, hsup, map_top_of_surjective _ (mk'_surjective M)]
      · intro i
        exact .of_mulEquiv (quotientSubgroupOfEquivMap (H i) M) ((ih i).2 (M.subgroupOf (H i)))

/-- Proposition 2.1 in the shape of Chou's sentence: closed under (I) and (II). -/
theorem constructible_subgroup_and_quotient' {G : Type u} [Group G] (h : Constructible G) :
    (∀ H : Subgroup G, Constructible H) ∧
      (∀ (N : Subgroup G) [N.Normal], Constructible (G ⧸ N)) :=
  constructible_closed h

theorem constructible_subgroup' {G : Type u} [Group G] (h : Constructible G) (H : Subgroup G) :
    Constructible H :=
  (constructible_closed h).1 H

theorem constructible_quotient' {G : Type u} [Group G] (h : Constructible G) (N : Subgroup G)
    [N.Normal] : Constructible (G ⧸ N) :=
  (constructible_closed h).2 N

theorem constructible_of_elementaryAmenable {G : Type u} [Group G] (h : ElementaryAmenable G) :
    Constructible G := by
  induction h with
  | @of_finite G _ _ => exact .of_finite G
  | @of_commGroup G _ => exact .of_commGroup G
  | @of_mulEquiv G H _ _ e _ ih => exact .of_mulEquiv e ih
  | @subgroup G _ H _ ih => exact constructible_subgroup' ih H
  | @quotient G _ N _ _ ih => exact constructible_quotient' ih N
  | @extension G _ N _ _ _ ihN ihQ => exact .extension N ihN ihQ
  | @directedUnion G _ ι H hdir hsup _ ih => exact .directedUnion H hdir hsup ih

theorem elementaryAmenable_of_constructible {G : Type u} [Group G] (h : Constructible G) :
    ElementaryAmenable G := by
  induction h with
  | @of_finite G _ _ => exact .of_finite G
  | @of_commGroup G _ => exact .of_commGroup G
  | @of_mulEquiv G H _ _ e _ ih => exact .of_mulEquiv e ih
  | @extension G _ N _ _ _ ihN ihQ => exact .extension N ihN ihQ
  | @directedUnion G _ ι H hdir hsup _ ih => exact .directedUnion H hdir hsup ih

/-- Proposition 2.2 (b). -/
theorem elementaryAmenable_iff_constructible' {G : Type u} [Group G] :
    ElementaryAmenable G ↔ Constructible G :=
  ⟨constructible_of_elementaryAmenable, elementaryAmenable_of_constructible⟩

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

lemma isLocallyFinite_subgroup {G : Type*} [Group G] (h : IsLocallyFinite G) (H : Subgroup G) :
    IsLocallyFinite H := by
  intro S hS
  haveI := h _ (hS.image H.subtype)
  have e := Subgroup.equivMapOfInjective (closure S) H.subtype (subtype_injective H)
  rw [MonoidHom.map_closure] at e
  exact Finite.of_equiv _ e.symm.toEquiv

lemma isLocallyFinite_quotient {G : Type*} [Group G] (h : IsLocallyFinite G) (N : Subgroup G)
    [N.Normal] : IsLocallyFinite (G ⧸ N) := by
  intro S hS
  have hsurj := mk'_surjective N
  have hST : (mk' N) '' (Function.surjInv hsurj '' S) = S := by
    rw [Set.image_image,
      show (fun x => (mk' N) (Function.surjInv hsurj x)) = id from
        funext (Function.surjInv_eq hsurj), Set.image_id]
  rw [← hST, ← MonoidHom.map_closure]
  haveI := h (Function.surjInv hsurj '' S) (hS.image _)
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
  isLocallyFinite_of_constructible (constructible_of_elementaryAmenable hG) ht

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

theorem noFreeSubgroupOfRankTwo_of_isMulTorsion' {G : Type*} [Group G] (ht : IsMulTorsion G) :
    NoFreeSubgroupOfRankTwo G := by
  intro f hf
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (ht (f (FreeGroup.of 0)))
  have h1 : (FreeGroup.of (0 : Fin 2)) ^ n = 1 := hf (by rw [map_pow, hpow, map_one])
  have h2 := congrArg (FreeGroup.lift (fun _ : Fin 2 => Multiplicative.ofAdd (1 : ℤ))) h1
  simp only [map_pow, FreeGroup.lift_apply_of, map_one, ← ofAdd_nsmul, ofAdd_eq_one,
    nsmul_eq_mul, mul_one] at h2
  omega

/-- Theorem 2.3, the step on p. 398: a non-locally finite periodic group lies in `NF \ EG`. -/
theorem noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite' {G : Type u} [Group G]
    (ht : IsMulTorsion G) (hnl : ¬ IsLocallyFinite G) :
    NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G :=
  ⟨noFreeSubgroupOfRankTwo_of_isMulTorsion' ht,
    fun hG => hnl (isLocallyFinite_of_elementaryAmenable_of_isMulTorsion' hG ht)⟩

open CannonFloydParry in
/-- Theorem 2.3, second statement, with Thompson's group `F` as the witness. -/
theorem exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable' :
    ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G := by
  refine ⟨F, inferInstance, ?_, not_elementaryAmenable_F⟩
  intro f hf
  apply no_free_subgroup_of_rank_two (f (FreeGroup.of 0) : UI ≃o UI) (f (FreeGroup.of 1))
    (f (FreeGroup.of 0)).2 (f (FreeGroup.of 1)).2
  have heq : FreeGroup.lift ![(f (FreeGroup.of 0) : UI ≃o UI), f (FreeGroup.of 1)]
      = F.subtype.comp f := by
    apply FreeGroup.ext_hom
    intro a
    fin_cases a <;> simp
  rw [heq]
  exact (subtype_injective _).comp hf

/-! ### Corollary 2.4 -/

theorem finite_of_constructible_of_isSimpleGroup {G : Type u} [Group G] (hG : Constructible G) :
    ∀ [Group.FG G] [IsSimpleGroup G], Finite G := by
  induction hG with
  | @of_finite G _ _ => intro _ _; infer_instance
  | @of_commGroup G _ => intro _ _; exact Nat.finite_of_card_ne_zero IsSimpleGroup.prime_card.ne_zero
  | @of_mulEquiv G H _ _ e _ ih =>
    intro _ _
    haveI : Group.FG G := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI : IsSimpleGroup G := e.isSimpleGroup
    haveI := ih
    exact Finite.of_equiv G e.toEquiv
  | @extension G _ N _ _ _ ihN ihQ =>
    intro _ _
    rcases ‹N.Normal›.eq_bot_or_eq_top with hN | hN
    · have e : G ⧸ N ≃* G := (quotientMulEquivOfEq hN).trans quotientBot
      haveI : Group.FG (G ⧸ N) := Group.fg_of_surjective (mk'_surjective N)
      haveI : IsSimpleGroup (G ⧸ N) := e.isSimpleGroup
      haveI := ihQ
      exact Finite.of_equiv _ e.toEquiv
    · have e : N ≃* G := (MulEquiv.subgroupCongr hN).trans Subgroup.topEquiv
      haveI : Group.FG N := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      haveI : IsSimpleGroup N := e.isSimpleGroup
      haveI := ihN
      exact Finite.of_equiv _ e.toEquiv
  | @directedUnion G _ ι H hdir hsup _ ih =>
    intro hfg _
    rcases isEmpty_or_nonempty ι with hι | hι
    · haveI := subsingleton_of_iSup_empty H hsup
      exact inferInstance
    · obtain ⟨S, hS⟩ := hfg.out
      obtain ⟨k, hk⟩ := exists_subset_of_directed hdir hsup (Finset.finite_toSet S)
      have htop : H k = ⊤ := by
        rw [eq_top_iff, ← hS]
        exact (closure_le _).mpr hk
      have e : H k ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      haveI : Group.FG (H k) := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      haveI : IsSimpleGroup (H k) := e.isSimpleGroup
      haveI := ih k
      exact Finite.of_equiv _ e.toEquiv

/-- Corollary 2.4. -/
theorem finite_of_elementaryAmenable_of_isSimpleGroup_of_fg' {G : Type u} [Group G]
    (hG : ElementaryAmenable G) [Group.FG G] [IsSimpleGroup G] : Finite G :=
  finite_of_constructible_of_isSimpleGroup (constructible_of_elementaryAmenable hG)

end Lib
end Chou

open Chou

theorem solution :
    ∃ (G : Type) (_ : Group G), NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G :=
  Chou.Lib.exists_noFreeSubgroupOfRankTwo_not_elementaryAmenable'
