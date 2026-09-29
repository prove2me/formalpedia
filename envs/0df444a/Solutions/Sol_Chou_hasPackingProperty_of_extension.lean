-- Prove2me | solution 1 for Chou.hasPackingProperty_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:18:30.801391+00:00
-- url     : https://prove2.me/submissions/55604825-422d-4011-9c5c-020be46c37fe

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

theorem hasPackingProperty_of_extension' {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : HasPackingProperty N) (hQ : HasPackingProperty (G ⧸ N)) : HasPackingProperty G := by
  classical
  intro F hF
  have hsurj : Function.Surjective (mk' N) := mk'_surjective N
  -- `F₁`: one representative in `F` for each class in `θ '' F`
  set F₁ : Set G := Function.invFunOn (mk' N) F '' ((mk' N) '' F) with hF₁
  have hF₁F : F₁ ⊆ F := by
    rintro _ ⟨c, ⟨p, hp, rfl⟩, rfl⟩
    exact Function.invFunOn_mem ⟨p, hp, rfl⟩
  have hθF₁ : Set.InjOn (mk' N) F₁ := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ h
    obtain ⟨p, hp, rfl⟩ := hc
    obtain ⟨p', hp', rfl⟩ := hc'
    rw [Function.invFunOn_eq (f := (mk' N)) ⟨p, hp, rfl⟩,
      Function.invFunOn_eq (f := (mk' N)) ⟨p', hp', rfl⟩] at h
    rw [h]
  have hF₁fin : F₁.Finite := (hF.image _).image _
  -- `E`: the elements `q⁻¹ p` of `N`
  set E : Set N := Subtype.val ⁻¹' ((fun p : G × G => p.1⁻¹ * p.2) '' (F₁ ×ˢ F)) with hE
  have hEfin : E.Finite := ((hF₁fin.prod hF).image _).preimage Subtype.val_injective.injOn
  obtain ⟨T, Y, hET, hTfin, hTY⟩ := hN E hEfin
  obtain ⟨U₁, X₁, hFU₁, hU₁fin, hU₁X₁⟩ := hQ ((mk' N) '' F) (hF.image _)
  rw [isPacking_iff] at hTY hU₁X₁
  obtain ⟨U, hF₁U, hUinj, hUim, hUfin⟩ :=
    exists_lift (mk' N) hsurj F₁ hθF₁ U₁ ((Set.image_mono hF₁F).trans hFU₁)
  obtain ⟨X, -, hXinj, hXim, -⟩ :=
    exists_lift (mk' N) hsurj ∅ (Set.injOn_empty _) X₁ (by simp)
  have hθU : ∀ u ∈ U, (mk' N) u ∈ U₁ := fun u hu => hUim ▸ ⟨u, hu, rfl⟩
  have hθX : ∀ x ∈ X, (mk' N) x ∈ X₁ := fun x hx => hXim ▸ ⟨x, hx, rfl⟩
  refine ⟨(fun p : G × N => p.1 * (p.2 : G)) '' (U ×ˢ T),
    (fun p : N × G => (p.1 : G) * p.2) '' (Y ×ˢ X), ?_, ?_, (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
  · -- `F ⊆ U T`
    intro p hp
    set q := Function.invFunOn (mk' N) F ((mk' N) p) with hq
    have hqF₁ : q ∈ F₁ := ⟨(mk' N) p, ⟨p, hp, rfl⟩, rfl⟩
    have hθq : (mk' N) q = (mk' N) p := Function.invFunOn_eq (f := (mk' N)) ⟨p, hp, rfl⟩
    have hmem : q⁻¹ * p ∈ N := (QuotientGroup.eq).mp hθq
    refine ⟨(q, ⟨q⁻¹ * p, hmem⟩), ⟨hF₁U hqF₁, hET ⟨(q, p), ⟨hqF₁, hp⟩, rfl⟩⟩, ?_⟩
    simp
  · exact ((hUfin hF₁fin hU₁fin).prod hTfin).image _
  · -- injectivity
    rintro _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩ _ ⟨⟨y, x⟩, ⟨hy, hx⟩, rfl⟩ _ ⟨⟨u', t'⟩, ⟨hu', ht'⟩, rfl⟩ _
      ⟨⟨y', x'⟩, ⟨hy', hx'⟩, rfl⟩ hh
    simp only at hh
    have hθ1 : (mk' N) u * (mk' N) x = (mk' N) u' * (mk' N) x' := by
      have := congrArg (mk' N) hh
      simp only [map_mul] at this
      rwa [show (mk' N) (t : G) = 1 from (QuotientGroup.eq_one_iff _).mpr t.2,
        show (mk' N) (y : G) = 1 from (QuotientGroup.eq_one_iff _).mpr y.2,
        show (mk' N) (t' : G) = 1 from (QuotientGroup.eq_one_iff _).mpr t'.2,
        show (mk' N) (y' : G) = 1 from (QuotientGroup.eq_one_iff _).mpr y'.2,
        mul_one, one_mul, mul_one, one_mul] at this
    obtain ⟨hu_eq, hx_eq⟩ :=
      hU₁X₁.1 _ (hθU u hu) _ (hθX x hx) _ (hθU u' hu') _ (hθX x' hx') hθ1
    have hu2 : u = u' := hUinj hu hu' hu_eq
    have hx2 : x = x' := hXinj hx hx' hx_eq
    subst hu2; subst hx2
    have hty : (t : G) * y = t' * y' := by
      have h3 : u * ((t : G) * ((y : G) * x)) = u * ((t' : G) * ((y' : G) * x)) := by
        simpa only [mul_assoc] using hh
      have h4 := mul_left_cancel h3
      rw [← mul_assoc, ← mul_assoc] at h4
      exact mul_right_cancel h4
    obtain ⟨rfl, rfl⟩ := hTY.1 t ht y hy t' ht' y' hy' (Subtype.ext hty)
    exact ⟨rfl, rfl⟩
  · -- surjectivity
    intro g
    obtain ⟨c, hc, d, hd, hcd⟩ := hU₁X₁.2 ((mk' N) g)
    obtain ⟨u, hu, rfl⟩ : c ∈ (mk' N) '' U := hUim ▸ hc
    obtain ⟨x, hx, rfl⟩ : d ∈ (mk' N) '' X := hXim ▸ hd
    have hmem : u⁻¹ * g * x⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      show (mk' N) (u⁻¹ * g * x⁻¹) = 1
      rw [map_mul, map_mul, map_inv, map_inv, ← hcd]
      group
    obtain ⟨t, ht, y, hy, hty⟩ := hTY.2 ⟨u⁻¹ * g * x⁻¹, hmem⟩
    refine ⟨u * t, ⟨(u, t), ⟨hu, ht⟩, rfl⟩, y * x, ⟨(y, x), ⟨hy, hx⟩, rfl⟩, ?_⟩
    have : (t : G) * y = u⁻¹ * g * x⁻¹ := congrArg Subtype.val hty
    calc u * (t : G) * ((y : G) * x) = u * ((t : G) * y) * x := by group
      _ = g := by rw [this]; group

/-! ### Lemma 4.6 (a) -/

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : HasPackingProperty N) (hQ : HasPackingProperty (G ⧸ N)) : HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_extension' N hN hQ
