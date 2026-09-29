-- Prove2me | solution 1 for Chou.hasPackingProperty_of_elementaryAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:17:26.728807+00:00
-- url     : https://prove2.me/submissions/9f858cb9-6b0e-4a0a-85aa-5d82075c7666

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib
import Theorems.Thm_Chou_hasPackingProperty_of_finite
import Theorems.Thm_Chou_hasPackingProperty_of_directedUnion
import Theorems.Thm_Chou_hasPackingProperty_of_extension
import Theorems.Thm_Chou_hasPackingProperty_of_commGroup_of_fg

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

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

/-! ### Locally finite groups -/

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

/-! ### Corollary 2.4 -/

end Lib
end Chou

/-! # Chou §4: packings and property (P) — the basic cases and Lemmas 4.1, 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Packings -/

lemma isPacking_iff {G : Type*} [Group G] (S X : Set G) :
    IsPacking S X ↔ (∀ s ∈ S, ∀ x ∈ X, ∀ s' ∈ S, ∀ x' ∈ X, s * x = s' * x' → s = s' ∧ x = x') ∧
      (∀ g : G, ∃ s ∈ S, ∃ x ∈ X, s * x = g) := by
  constructor
  · rintro ⟨-, hinj, hsurj⟩
    refine ⟨fun s hs x hx s' hs' x' hx' h => ?_, fun g => ?_⟩
    · have := @hinj (s, x) ⟨hs, hx⟩ (s', x') ⟨hs', hx'⟩ h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · obtain ⟨⟨s, x⟩, ⟨hs, hx⟩, h⟩ := hsurj (Set.mem_univ g)
      exact ⟨s, hs, x, hx, h⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro ⟨s, x⟩ ⟨hs, hx⟩ ⟨s', x'⟩ ⟨hs', hx'⟩ h
      obtain ⟨rfl, rfl⟩ := hinj s hs x hx s' hs' x' hx' h
      rfl
    · intro g _
      obtain ⟨s, hs, x, hx, h⟩ := hsurj g
      exact ⟨(s, x), ⟨hs, hx⟩, h⟩

lemma isPacking_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {S X : Set G}
    (h : IsPacking S X) : IsPacking (e '' S) (e '' X) := by
  rw [isPacking_iff] at h ⊢
  obtain ⟨hinj, hsurj⟩ := h
  refine ⟨?_, fun g => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩ _ ⟨s', hs', rfl⟩ _ ⟨x', hx', rfl⟩ hh
    rw [← map_mul, ← map_mul] at hh
    obtain ⟨rfl, rfl⟩ := hinj s hs x hx s' hs' x' hx' (e.injective hh)
    exact ⟨rfl, rfl⟩
  · obtain ⟨s, hs, x, hx, h⟩ := hsurj (e.symm g)
    exact ⟨e s, ⟨s, hs, rfl⟩, e x, ⟨x, hx, rfl⟩, by rw [← map_mul, h, MulEquiv.apply_symm_apply]⟩

theorem hasPackingProperty_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : HasPackingProperty G) : HasPackingProperty H := by
  intro F hF
  obtain ⟨S, X, hFS, hS, hp⟩ := h (e.symm '' F) (hF.image _)
  refine ⟨e '' S, e '' X, ?_, hS.image _, isPacking_map e hp⟩
  intro f hf
  exact ⟨e.symm f, hFS ⟨f, hf, rfl⟩, MulEquiv.apply_symm_apply e f⟩

/-! ### Finite groups and the integers -/



/-! ### Lemma 4.1 (a): directed unions -/


end Lib
end Chou

/-! # Chou §4: Lemma 4.1 (b) (extensions) and Lemma 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Lemma 4.1 (b) -/


/-! ### Lemma 4.6 (a) -/

end Lib
end Chou

/-! # Chou §4: finitely generated abelian groups, Proposition 4.2, Corollary 4.7 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Products -/

/-! ### Abelian groups -/


theorem hasPackingProperty_of_commGroup {G : Type*} [CommGroup G] : HasPackingProperty G := by
  classical
  refine Chou.hasPackingProperty_of_directedUnion (fun s : Finset G => closure (s : Set G)) ?_ ?_ ?_
  · intro s t
    exact ⟨s ∪ t, closure_mono (by simp), closure_mono (by simp)⟩
  · rw [eq_top_iff]
    intro g _
    exact mem_iSup_of_mem {g} (subset_closure (by simp))
  · intro s
    exact Chou.hasPackingProperty_of_commGroup_of_fg

/-! ### Proposition 4.2 -/

theorem hasPackingProperty_of_constructible {G : Type u} [Group G] (hG : Constructible G) :
    HasPackingProperty G := by
  induction hG with
  | @of_finite G _ _ => exact Chou.hasPackingProperty_of_finite
  | @of_commGroup G _ => exact hasPackingProperty_of_commGroup
  | @of_mulEquiv G H _ _ e _ ih => exact hasPackingProperty_of_mulEquiv e ih
  | @extension G _ N _ _ _ ihN ihQ => exact Chou.hasPackingProperty_of_extension N ihN ihQ
  | @directedUnion G _ ι H hdir hsup _ ih => exact Chou.hasPackingProperty_of_directedUnion H hdir hsup ih

theorem hasPackingProperty_of_elementaryAmenable' {G : Type u} [Group G] (hG : ElementaryAmenable G) :
    HasPackingProperty G :=
  hasPackingProperty_of_constructible (constructible_of_elementaryAmenable hG)

/-! ### Corollary 4.7 -/

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (hG : ElementaryAmenable G) :
    HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_elementaryAmenable' hG
