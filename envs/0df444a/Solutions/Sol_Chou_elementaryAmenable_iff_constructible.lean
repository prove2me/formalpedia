-- Prove2me | solution 1 for Chou.elementaryAmenable_iff_constructible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T12:05:58.23116+00:00
-- url     : https://prove2.me/submissions/b3975d4f-2116-4696-8cd5-3b580eb4ee5f

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

open Chou

theorem solution {G : Type*} [Group G] : ElementaryAmenable G ↔ Constructible G :=
  Chou.Lib.elementaryAmenable_iff_constructible'
