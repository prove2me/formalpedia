-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:41:54.393455+00:00
-- url     : https://prove2.me/submissions/10ced551-566b-4e1c-ae3c-23f0c5999393

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
import Theorems.Thm_CategoryTheory_SequentialSystem_epi_map_of_epi_transition

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

/-- If the successive transition maps of a system of abelian groups are surjective,
then so are all the maps `F.obj (op n) ⟶ F.obj (op m)` for `m ≤ n`. -/
lemma surjective_map_of_surjective_transition {F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (hF : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition F n)))
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (ConcreteCategory.hom (F.map (homOfLE hmn).op)) := by
  have hepi : ∀ n', Epi (SequentialSystem.transition F n') := fun n' ↦
    (AddCommGrpCat.epi_iff_surjective _).mpr (hF n')
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (SequentialSystem.epi_map_of_epi_transition F hepi hmn)

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


/-- **Mittag-Leffler for a quotient-like term.** Suppose `B ⟶ C ⟶ D` are maps of
inverse systems of abelian groups which are levelwise exact at `C` (`range g = ker h`),
`h` is levelwise surjective, the transition maps of `B` are surjective, and `D`
satisfies the Mittag-Leffler condition. Then `C` satisfies the Mittag-Leffler
condition. -/
lemma isMittagLeffler_of_exact
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hD : (D ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at hD ⊢
  intro n
  obtain ⟨m, hm, hstab⟩ := hD n
  refine ⟨m, hm, fun k hk c ↦ ?_⟩
  obtain ⟨d', hd'⟩ := hstab k hk (ConcreteCategory.hom (h.app (op m)) c)
  obtain ⟨c', hc'⟩ := hsurj (op k) d'
  have hnat1 : ConcreteCategory.hom (h.app (op n))
      (ConcreteCategory.hom (C.map (homOfLE hk).op) c') =
      ConcreteCategory.hom (D.map (homOfLE hk).op) d' := by
    calc ConcreteCategory.hom (h.app (op n))
          (ConcreteCategory.hom (C.map (homOfLE hk).op) c')
        = ConcreteCategory.hom (C.map (homOfLE hk).op ≫ h.app (op n)) c' :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (h.app (op k) ≫ D.map (homOfLE hk).op) c' :=
          ConcreteCategory.congr_hom (h.naturality (homOfLE hk).op) c'
      _ = ConcreteCategory.hom (D.map (homOfLE hk).op)
            (ConcreteCategory.hom (h.app (op k)) c') :=
          ConcreteCategory.comp_apply _ _ _
      _ = ConcreteCategory.hom (D.map (homOfLE hk).op) d' := by rw [hc']
  have hnat2 : ConcreteCategory.hom (h.app (op n))
      (ConcreteCategory.hom (C.map (homOfLE hm).op) c) =
      ConcreteCategory.hom (D.map (homOfLE hm).op)
        (ConcreteCategory.hom (h.app (op m)) c) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (h.naturality (homOfLE hm).op) c).trans
        (ConcreteCategory.comp_apply _ _ _))
  have hzero : ConcreteCategory.hom (h.app (op n))
      (ConcreteCategory.hom (C.map (homOfLE hk).op) c' -
        ConcreteCategory.hom (C.map (homOfLE hm).op) c) = 0 := by
    rw [map_sub, hnat1, hnat2, hd', sub_self]
  obtain ⟨b, hb⟩ := hexact (op n) _ hzero
  obtain ⟨b', hb'⟩ := surjective_map_of_surjective_transition hB hk b
  refine ⟨c' - ConcreteCategory.hom (g.app (op k)) b', ?_⟩
  have hgnat : ConcreteCategory.hom (C.map (homOfLE hk).op)
      (ConcreteCategory.hom (g.app (op k)) b') =
      ConcreteCategory.hom (C.map (homOfLE hk).op) c' -
        ConcreteCategory.hom (C.map (homOfLE hm).op) c := by
    calc ConcreteCategory.hom (C.map (homOfLE hk).op)
          (ConcreteCategory.hom (g.app (op k)) b')
        = ConcreteCategory.hom (g.app (op k) ≫ C.map (homOfLE hk).op) b' :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (B.map (homOfLE hk).op ≫ g.app (op n)) b' :=
          (ConcreteCategory.congr_hom (g.naturality (homOfLE hk).op) b').symm
      _ = ConcreteCategory.hom (g.app (op n))
            (ConcreteCategory.hom (B.map (homOfLE hk).op) b') :=
          ConcreteCategory.comp_apply _ _ _
      _ = ConcreteCategory.hom (g.app (op n)) b := by rw [hb']
      _ = _ := hb
  rw [map_sub, hgnat]
  abel


end AbChase


end Ext
end Abelian
end CategoryTheory


theorem solution.{sol_u1} : type_of% @CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact.{sol_u1} := @CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact.{sol_u1}
