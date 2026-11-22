-- Prove2me | solution 1 for CGSpace.isRegularEpi_effectiveEpi_isQuotientMap_tfae
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:06:49.095023+00:00
-- url     : https://prove2.me/submissions/027a0587-f0ad-4cb1-a312-f53e36408a86

import Mathlib

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u w

namespace Sol_CGSpace_isRegularEpi_effectiveEpi_isQuotientMap_tfae

/-- An effective epimorphism of compactly generated spaces is a quotient map: compare the
target with the quotient of the source by the kernel relation of the map. -/
theorem isQuotientMap_of_effectiveEpi {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y)
    [EffectiveEpi f] : IsQuotientMap (ConcreteCategory.hom f) := by
  -- the quotient `Q = X / ker f`, which is compactly generated
  let S : Setoid X := Setoid.ker (ConcreteCategory.hom f)
  let Q : CompactlyGenerated.{u, w} := CompactlyGenerated.of (Quotient S)
  let q : X ⟶ Q := CompactlyGenerated.ofHom ⟨Quotient.mk S, continuous_quotient_mk'⟩
  -- the canonical continuous injection `g : Q → Y`
  let g : Q ⟶ Y := CompactlyGenerated.ofHom
    ⟨Quotient.lift (ConcreteCategory.hom f) (fun _ _ h => h),
      (ConcreteCategory.hom f).continuous.quotient_lift _⟩
  have hqg : q ≫ g = f := by
    ext x
    rfl
  -- `q` coequalizes every pair of morphisms that `f` coequalizes
  have hq : ∀ {Z : CompactlyGenerated.{u, w}} (g₁ g₂ : Z ⟶ X),
      g₁ ≫ f = g₂ ≫ f → g₁ ≫ q = g₂ ≫ q := by
    intro Z g₁ g₂ h
    ext z
    have hz : (ConcreteCategory.hom f) ((ConcreteCategory.hom g₁) z)
        = (ConcreteCategory.hom f) ((ConcreteCategory.hom g₂) z) :=
      ConcreteCategory.congr_hom h z
    exact Quotient.sound hz
  -- hence `q` descends along `f`
  let d : Y ⟶ Q := EffectiveEpi.desc f q hq
  have hfd : f ≫ d = q := EffectiveEpi.fac f q hq
  have hdg : d ≫ g = 𝟙 Y := by
    rw [← cancel_epi f, ← Category.assoc, hfd, hqg, Category.comp_id]
  have hdg' : ∀ y : Y, (ConcreteCategory.hom g) ((ConcreteCategory.hom d) y) = y := fun y =>
    ConcreteCategory.congr_hom hdg y
  have hgq : ∀ x : X, (ConcreteCategory.hom g) (Quotient.mk S x) = (ConcreteCategory.hom f) x :=
    fun _ => rfl
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun V =>
    ⟨fun hV => ?_, fun hV => hV.preimage (ConcreteCategory.hom f).continuous⟩, fun y => ?_⟩
  · -- `g ⁻¹' V` is open in the quotient, and `V = d ⁻¹' (g ⁻¹' V)`
    have hopen : IsOpen ((ConcreteCategory.hom g) ⁻¹' V) := by
      rw [← (isQuotientMap_quotient_mk' (s := S)).isOpen_preimage]
      exact hV
    have hpre : V = (ConcreteCategory.hom d) ⁻¹' ((ConcreteCategory.hom g) ⁻¹' V) := by
      ext y
      simp only [Set.mem_preimage]
      rw [hdg' y]
    rw [hpre]
    exact hopen.preimage (ConcreteCategory.hom d).continuous
  · -- surjectivity: `y = g (d y)` and `d y` is the class of some `x`
    obtain ⟨x, hx⟩ := Quotient.exists_rep ((ConcreteCategory.hom d) y)
    refine ⟨x, ?_⟩
    rw [← hgq x, hx, hdg' y]

/-- A quotient map of compactly generated spaces is a regular epimorphism: it is the
coequalizer of the two projections of its kernel relation, given the discrete topology. -/
theorem isRegularEpi_of_isQuotientMap {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y)
    (hf : IsQuotientMap (ConcreteCategory.hom f)) : IsRegularEpi f := by
  -- the kernel relation of `f` as a discrete (hence compactly generated) space
  let R : Type w := {p : X × X // (ConcreteCategory.hom f) p.1 = (ConcreteCategory.hom f) p.2}
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let W : CompactlyGenerated.{u, w} := CompactlyGenerated.of R
  let s : W ⟶ X := CompactlyGenerated.ofHom
    ⟨fun p : R => p.1.1, continuous_of_discreteTopology⟩
  let t : W ⟶ X := CompactlyGenerated.ofHom
    ⟨fun p : R => p.1.2, continuous_of_discreteTopology⟩
  have hw : s ≫ f = t ≫ f := by
    ext p
    exact p.2
  -- the underlying continuous map of the leg of a cofork on `(s, t)`
  let leg : ∀ c : Limits.Cofork s t, C(X, c.pt) := fun c => c.π.hom.hom
  -- a morphism coequalizing `s` and `t` is constant on the fibres of `f`
  have key : ∀ (c : Limits.Cofork s t),
      Function.FactorsThrough (leg c) (ConcreteCategory.hom f) := by
    intro c a b hab
    exact ConcreteCategory.congr_hom c.condition (⟨(a, b), hab⟩ : R)
  have hlift : ∀ (c : Limits.Cofork s t) (x : X),
      (hf.lift (leg c) (key c)) ((ConcreteCategory.hom f) x) = leg c x := fun c x =>
    DFunLike.congr_fun (hf.lift_comp (leg c) (key c)) x
  refine ⟨⟨{ W := W, left := s, right := t, w := hw, isColimit := ?_ }⟩⟩
  refine Limits.Cofork.IsColimit.mk _
    (fun c : Limits.Cofork s t => CompactlyGenerated.ofHom (hf.lift (leg c) (key c))) ?_ ?_
  · intro c
    ext x
    exact hlift c x
  · intro c m hm
    ext y
    obtain ⟨x, rfl⟩ := hf.surjective y
    have h1 : (ConcreteCategory.hom m) ((ConcreteCategory.hom f) x) = leg c x :=
      ConcreteCategory.congr_hom hm x
    exact h1.trans (hlift c x).symm

end Sol_CGSpace_isRegularEpi_effectiveEpi_isQuotientMap_tfae

open Sol_CGSpace_isRegularEpi_effectiveEpi_isQuotientMap_tfae in
theorem solution
    {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    [IsRegularEpi f, EffectiveEpi f, IsQuotientMap (ConcreteCategory.hom f)].TFAE := by
  tfae_have 1 → 2 := fun h => inferInstance
  tfae_have 2 → 3 := fun h => isQuotientMap_of_effectiveEpi f
  tfae_have 3 → 1 := fun h => isRegularEpi_of_isQuotientMap f h
  tfae_finish
