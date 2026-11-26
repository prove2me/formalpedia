-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:41:37.826132+00:00
-- url     : https://prove2.me/submissions/65033878-b241-4ea3-813f-c008c439d32e

import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit
import Theorems.Thm_CategoryTheory_Functor_isMittagLeffler_nat_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# `Ext` out of a constant system versus the limit of levelwise `Ext`-groups

Let `A` be an abelian category with enough injectives and countable products, and let
`Z : A`. For an inverse system `F : ℕᵒᵖ ⥤ A` we compare the `Ext`-groups
`Ext (Δ Z) F i` in the category of inverse systems (the right derived functors of
`F ↦ lim Hom(Z, Fₙ)`, e.g. continuous étale cohomology) with the inverse limit of the
levelwise `Ext`-groups `Ext Z Fₙ i`.

In general the two differ by a `lim¹`-term (Jannsen). We prove the comparison
isomorphism in degree `0` unconditionally, and in degree `i + 1` under the hypothesis
that the degree-`i` levelwise `Ext`-system satisfies the Mittag-Leffler condition
(`CategoryTheory.Functor.IsMittagLeffler`, which forces the relevant `lim¹` to
vanish); the latter holds in particular when the transition maps of that system are
surjective, or when its groups are finite:

- `CategoryTheory.Abelian.Ext.zeroAddEquivLimitLevelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem_of_surjective`

The proof is by dimension shifting along `0 → F → I → Q → 0` with `I` injective: the
degree-one case is an explicit Mittag-Leffler eventual-image argument for the
four-term exact sequences of systems
`0 → Hom(Z,F•) → Hom(Z,I•) → Hom(Z,Q•) → Ext¹(Z,F•) → 0`
(using that the transition maps of `Hom(Z,I•)` are split surjections), and the
inductive step uses the connecting isomorphisms on both sides, with naturality in the
system direction provided by `ShortComplex.ShortExact.extClass_naturality`.
-/

universe w t v u

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian
namespace Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]


section AbChase

/-! ### Two Mittag-Leffler-type diagram chases for systems of abelian groups -/

variable {B C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (g : B ⟶ C) (h : C ⟶ D)


/-! #### The Mittag-Leffler condition for systems of abelian groups -/


/-- The Mittag-Leffler condition for an `ℕᵒᵖ`-indexed system of abelian groups,
elementwise: for every level `n` there is an `m ≥ n` such that the image of any
element of level `m` in level `n` is also in the image of every level `k ≥ n`. -/
lemma isMittagLeffler_forget_iff (C : ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler ↔
      ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
        ∀ x : ToType (C.obj (op m)), ∃ y : ToType (C.obj (op k)),
          ConcreteCategory.hom (C.map (homOfLE hk).op) y =
            ConcreteCategory.hom (C.map (homOfLE hm).op) x := by
  rw [Functor.isMittagLeffler_nat_iff]
  refine forall_congr' fun n ↦ exists_congr fun m ↦ exists_congr fun hm ↦
    forall_congr' fun k ↦ forall_congr' fun hk ↦ ?_
  constructor
  · intro hsub x
    obtain ⟨y, hy⟩ := hsub (Set.mem_range_self x)
    exact ⟨y, hy⟩
  · rintro hx _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx x
    exact ⟨y, hy⟩


/-- The Mittag-Leffler condition descends along a levelwise bijective morphism of
systems of abelian groups. -/
lemma isMittagLeffler_forget_of_app_bijective {C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (φ : C ⟶ D) (hφ : ∀ k, Function.Bijective (ConcreteCategory.hom (φ.app k)))
    (hD : (D ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at hD ⊢
  intro n
  obtain ⟨m, hm, hstab⟩ := hD n
  refine ⟨m, hm, fun k hk x ↦ ?_⟩
  obtain ⟨yD, hyD⟩ := hstab k hk (ConcreteCategory.hom (φ.app (op m)) x)
  obtain ⟨y, rfl⟩ := (hφ (op k)).2 yD
  refine ⟨y, (hφ (op n)).1 ?_⟩
  have h1 : ConcreteCategory.hom (φ.app (op n))
      (ConcreteCategory.hom (C.map (homOfLE hk).op) y) =
      ConcreteCategory.hom (D.map (homOfLE hk).op)
        (ConcreteCategory.hom (φ.app (op k)) y) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (φ.naturality (homOfLE hk).op) y).trans
        (ConcreteCategory.comp_apply _ _ _))
  have h2 : ConcreteCategory.hom (φ.app (op n))
      (ConcreteCategory.hom (C.map (homOfLE hm).op) x) =
      ConcreteCategory.hom (D.map (homOfLE hm).op)
        (ConcreteCategory.hom (φ.app (op m)) x) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (φ.naturality (homOfLE hm).op) x).trans
        (ConcreteCategory.comp_apply _ _ _))
  exact h1.trans (hyD.trans h2.symm)


end AbChase


end Ext
end Abelian
end CategoryTheory


theorem solution.{sol_u1} : type_of% @CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective.{sol_u1} := @CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective.{sol_u1}
