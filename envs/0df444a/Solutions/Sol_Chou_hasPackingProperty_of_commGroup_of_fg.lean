-- Prove2me | solution 1 for Chou.hasPackingProperty_of_commGroup_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:12:28.313474+00:00
-- url     : https://prove2.me/submissions/e65dcca9-a80a-494a-aac3-7057b1e806d7

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib
import Theorems.Thm_Chou_hasPackingProperty_of_finite
import Theorems.Thm_Chou_hasPackingProperty_int

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

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

theorem hasPackingProperty_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, Group (G i)]
    (h : ∀ i, HasPackingProperty (G i)) : HasPackingProperty (∀ i, G i) := by
  classical
  intro F hF
  choose S X hFS hSfin hSX using fun i => h i ((fun f => f i) '' F) (hF.image _)
  simp_rw [isPacking_iff] at hSX
  refine ⟨Set.pi Set.univ S, Set.pi Set.univ X, ?_, Set.Finite.pi hSfin,
    (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
  · intro f hf i _
    exact hFS i ⟨f, hf, rfl⟩
  · intro s hs x hx s' hs' x' hx' hh
    constructor <;> funext i
    · exact ((hSX i).1 (s i) (hs i (Set.mem_univ _)) (x i) (hx i (Set.mem_univ _)) (s' i)
        (hs' i (Set.mem_univ _)) (x' i) (hx' i (Set.mem_univ _)) (congrFun hh i)).1
    · exact ((hSX i).1 (s i) (hs i (Set.mem_univ _)) (x i) (hx i (Set.mem_univ _)) (s' i)
        (hs' i (Set.mem_univ _)) (x' i) (hx' i (Set.mem_univ _)) (congrFun hh i)).2
  · intro g
    choose s hs x hx hsx using fun i => (hSX i).2 (g i)
    exact ⟨s, fun i _ => hs i, x, fun i _ => hx i, funext hsx⟩

theorem hasPackingProperty_prod {G H : Type*} [Group G] [Group H] (hG : HasPackingProperty G)
    (hH : HasPackingProperty H) : HasPackingProperty (G × H) := by
  intro F hF
  obtain ⟨S₁, X₁, hFS₁, hS₁, hp₁⟩ := hG (Prod.fst '' F) (hF.image _)
  obtain ⟨S₂, X₂, hFS₂, hS₂, hp₂⟩ := hH (Prod.snd '' F) (hF.image _)
  rw [isPacking_iff] at hp₁ hp₂
  refine ⟨S₁ ×ˢ S₂, X₁ ×ˢ X₂, ?_, hS₁.prod hS₂, (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
  · intro f hf
    exact ⟨hFS₁ ⟨f, hf, rfl⟩, hFS₂ ⟨f, hf, rfl⟩⟩
  · rintro ⟨s₁, s₂⟩ ⟨hs₁, hs₂⟩ ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨s₁', s₂'⟩ ⟨hs₁', hs₂'⟩ ⟨x₁', x₂'⟩ ⟨hx₁', hx₂'⟩ hh
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    obtain ⟨rfl, rfl⟩ := hp₁.1 s₁ hs₁ x₁ hx₁ s₁' hs₁' x₁' hx₁' h1
    obtain ⟨rfl, rfl⟩ := hp₂.1 s₂ hs₂ x₂ hx₂ s₂' hs₂' x₂' hx₂' h2
    exact ⟨rfl, rfl⟩
  · rintro ⟨g₁, g₂⟩
    obtain ⟨s₁, hs₁, x₁, hx₁, h1⟩ := hp₁.2 g₁
    obtain ⟨s₂, hs₂, x₂, hx₂, h2⟩ := hp₂.2 g₂
    exact ⟨(s₁, s₂), ⟨hs₁, hs₂⟩, (x₁, x₂), ⟨hx₁, hx₂⟩, Prod.ext h1 h2⟩

/-! ### Abelian groups -/

theorem hasPackingProperty_of_commGroup_of_fg' {G : Type*} [CommGroup G] [Group.FG G] :
    HasPackingProperty G := by
  classical
  haveI : AddGroup.FG (Additive G) :=
    AddGroup.fg_iff_addMonoid_fg.mpr (Monoid.fg_iff_add_fg.mp (Group.fg_iff_monoid_fg.mp inferInstance))
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (G := Additive G)
  have e1 : G ≃* Multiplicative ((Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i))) :=
    (MulEquiv.multiplicativeAdditive G).symm.trans (AddEquiv.toMultiplicative f)
  apply hasPackingProperty_of_mulEquiv e1.symm
  apply hasPackingProperty_of_mulEquiv
    (MulEquiv.prodMultiplicative (G := Fin n →₀ ℤ) (H := DirectSum ι (fun i => ZMod (p i ^ e i)))).symm
  apply hasPackingProperty_prod
  · apply hasPackingProperty_of_mulEquiv
      (AddEquiv.toMultiplicative (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv).symm
    apply hasPackingProperty_of_mulEquiv (MulEquiv.piMultiplicative _).symm
    exact hasPackingProperty_pi _ (fun _ => Chou.hasPackingProperty_int)
  · haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
    haveI : Finite (DirectSum ι (fun i => ZMod (p i ^ e i))) :=
      Finite.of_injective (fun x : DirectSum ι (fun i => ZMod (p i ^ e i)) => (x : ∀ i, ZMod (p i ^ e i)))
        DFunLike.coe_injective
    exact Chou.hasPackingProperty_of_finite

/-! ### Proposition 4.2 -/

/-! ### Corollary 4.7 -/

end Lib
end Chou

open Chou

theorem solution {G : Type*} [CommGroup G] [Group.FG G] : HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_commGroup_of_fg'
