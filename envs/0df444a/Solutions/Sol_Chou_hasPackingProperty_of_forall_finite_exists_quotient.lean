-- Prove2me | solution 1 for Chou.hasPackingProperty_of_forall_finite_exists_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:21:17.354253+00:00
-- url     : https://prove2.me/submissions/1cfab15a-8844-480c-a91c-58a093dbdb10

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

/-! ### Finite groups and the integers -/

/-! ### Lemma 4.1 (a): directed unions -/

end Lib
end Chou

/-! # Chou §4: Lemma 4.1 (b) (extensions) and Lemma 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-- Lifting a set through a surjection: given `F₀` on which `θ` is injective and `S₁ ⊇ θ '' F₀`,
a set `U ⊇ F₀` on which `θ` is injective with `θ '' U = S₁`. -/
lemma exists_lift {G Q : Type*} (θ : G → Q) (hsurj : Function.Surjective θ) (F₀ : Set G)
    (hinj : Set.InjOn θ F₀) (S₁ : Set Q) (hsub : θ '' F₀ ⊆ S₁) :
    ∃ U : Set G, F₀ ⊆ U ∧ Set.InjOn θ U ∧ θ '' U = S₁ ∧ (F₀.Finite → S₁.Finite → U.Finite) := by
  refine ⟨F₀ ∪ Function.surjInv hsurj '' (S₁ \ θ '' F₀), Set.subset_union_left, ?_, ?_, ?_⟩
  · rintro a (ha | ⟨c, ⟨hc, hcF⟩, rfl⟩) b (hb | ⟨d, ⟨hd, hdF⟩, rfl⟩) h
    · exact hinj ha hb h
    · exact absurd ⟨a, ha, by rw [h, Function.surjInv_eq hsurj]⟩ hdF
    · exact absurd ⟨b, hb, by rw [← h, Function.surjInv_eq hsurj]⟩ hcF
    · rw [Function.surjInv_eq hsurj, Function.surjInv_eq hsurj] at h
      rw [h]
  · apply Set.Subset.antisymm
    · rintro _ ⟨a, (ha | ⟨c, ⟨hc, _⟩, rfl⟩), rfl⟩
      · exact hsub ⟨a, ha, rfl⟩
      · rw [Function.surjInv_eq hsurj]; exact hc
    · intro c hc
      by_cases hcF : c ∈ θ '' F₀
      · obtain ⟨a, ha, rfl⟩ := hcF
        exact ⟨a, Or.inl ha, rfl⟩
      · exact ⟨Function.surjInv hsurj c, Or.inr ⟨c, ⟨hc, hcF⟩, rfl⟩, Function.surjInv_eq hsurj c⟩
  · intro h0 h1
    exact h0.union (h1.diff.image _)

/-! ### Lemma 4.1 (b) -/

/-! ### Lemma 4.6 (a) -/

theorem hasPackingProperty_of_forall_finite_exists_quotient' {G : Type*} [Group G]
    (h : ∀ F : Set G, F.Finite → ∃ (K : Subgroup G) (_ : K.Normal),
      HasPackingProperty (G ⧸ K) ∧ Set.InjOn (QuotientGroup.mk : G → G ⧸ K) F) :
    HasPackingProperty G := by
  intro F hF
  obtain ⟨K, hKn, hP, hinjF⟩ := h F hF
  have hsurj : Function.Surjective (QuotientGroup.mk : G → G ⧸ K) := QuotientGroup.mk_surjective
  obtain ⟨S₁, X₁, hFS₁, hS₁fin, hpack⟩ := hP (QuotientGroup.mk '' F) (hF.image _)
  rw [isPacking_iff] at hpack
  obtain ⟨S, hFS, hSinj, hSim, hSfin⟩ := exists_lift _ hsurj F hinjF S₁ hFS₁
  have hθS : ∀ s ∈ S, (QuotientGroup.mk s : G ⧸ K) ∈ S₁ := fun s hs => hSim ▸ ⟨s, hs, rfl⟩
  refine ⟨S, QuotientGroup.mk ⁻¹' X₁, hFS, hSfin hF hS₁fin, (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
  · intro s hs x hx s' hs' x' hx' hh
    have h1 : (QuotientGroup.mk s : G ⧸ K) * QuotientGroup.mk x
        = QuotientGroup.mk s' * QuotientGroup.mk x' := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hh]
    obtain ⟨h2, -⟩ := hpack.1 _ (hθS s hs) _ hx _ (hθS s' hs') _ hx' h1
    have hs_eq : s = s' := hSinj hs hs' h2
    subst hs_eq
    exact ⟨rfl, mul_left_cancel hh⟩
  · intro g
    obtain ⟨c, hc, d, hd, hcd⟩ := hpack.2 (QuotientGroup.mk g)
    obtain ⟨s, hs, rfl⟩ : c ∈ QuotientGroup.mk '' S := hSim ▸ hc
    refine ⟨s, hs, s⁻¹ * g, ?_, by group⟩
    show (QuotientGroup.mk (s⁻¹ * g) : G ⧸ K) ∈ X₁
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hcd, inv_mul_cancel_left]
    exact hd

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G]
    (h : ∀ F : Set G, F.Finite → ∃ (K : Subgroup G) (_ : K.Normal),
      HasPackingProperty (G ⧸ K) ∧ Set.InjOn (QuotientGroup.mk : G → G ⧸ K) F) :
    HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_forall_finite_exists_quotient' h
