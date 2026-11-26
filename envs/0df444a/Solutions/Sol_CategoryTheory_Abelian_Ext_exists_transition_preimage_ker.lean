-- Prove2me | solution 1 for CategoryTheory.Abelian.Ext.exists_transition_preimage_ker
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:41:34.474121+00:00
-- url     : https://prove2.me/submissions/8b602403-baf8-460b-b169-c3bd4545a532

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


end AbChase

section Main

variable [EnoughInjectives A] [HasProductsOfShape ℕ A]

variable (Z : A)


variable {SC : ShortComplex (ℕᵒᵖ ⥤ A)}


omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Relative Mittag-Leffler input for `surjective_limMap_and_exact`: under the
Mittag-Leffler hypothesis on `Hom(Z, SC.X₁•)`, the kernels of the level maps from the
level system of the middle object to that of the third object satisfy the stabilized
elementwise Mittag-Leffler condition. -/
lemma exists_transition_preimage_ker
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact)
    (hML : (levelSystem Z SC.X₁ 0 ⋙
      CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      ∀ b : Ext Z (SC.X₂.obj (op m)) 0,
        ConcreteCategory.hom
          ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op m)) b = 0 →
        ∃ b' : Ext Z (SC.X₂.obj (op k)) 0,
          ConcreteCategory.hom
            ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op k)) b' = 0 ∧
          ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hk).op) b' =
            ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hm).op) b := by
  rw [isMittagLeffler_forget_iff] at hML
  intro n
  obtain ⟨m, hm, hstab⟩ := hML n
  refine ⟨m, hm, fun k hk b hb ↦ ?_⟩
  obtain ⟨w, hw⟩ := covariant_sequence_exact₂ Z (hSCk (op m)) b
    ((whiskerRight_extFunctorObj_app_apply Z 0 (op m) b).symm.trans hb)
  obtain ⟨w', hw'⟩ := hstab k hk w
  have hw'' : w'.comp (Ext.mk₀ (SC.X₁.map (homOfLE hk).op)) (add_zero 0) =
      w.comp (Ext.mk₀ (SC.X₁.map (homOfLE hm).op)) (add_zero 0) :=
    (levelSystem_map_apply 0 _ _).symm.trans
      (hw'.trans (levelSystem_map_apply 0 _ _))
  refine ⟨w'.comp (Ext.mk₀ (SC.f.app (op k))) (add_zero 0), ?_, ?_⟩
  · have h2 : SC.f.app (op k) ≫ SC.g.app (op k) = 0 := by
      rw [← NatTrans.comp_app, SC.zero, zero_app]
    calc ConcreteCategory.hom
          ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op k))
          (w'.comp (Ext.mk₀ (SC.f.app (op k))) (add_zero 0))
        = (w'.comp (Ext.mk₀ (SC.f.app (op k))) (add_zero 0)).comp
            (Ext.mk₀ (SC.g.app (op k))) (add_zero 0) := rfl
      _ = w'.comp ((Ext.mk₀ (SC.f.app (op k))).comp
            (Ext.mk₀ (SC.g.app (op k))) (zero_add 0)) (add_zero 0) :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = 0 := by rw [Ext.mk₀_comp_mk₀, h2, Ext.mk₀_zero, Ext.comp_zero]
  · calc ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hk).op)
          (w'.comp (Ext.mk₀ (SC.f.app (op k))) (add_zero 0))
        = (w'.comp (Ext.mk₀ (SC.f.app (op k))) (add_zero 0)).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE hk).op)) (add_zero 0) := rfl
      _ = w'.comp ((Ext.mk₀ (SC.f.app (op k))).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE hk).op)) (zero_add 0))
            (add_zero 0) := Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = w'.comp ((Ext.mk₀ (SC.X₁.map (homOfLE hk).op)).comp
            (Ext.mk₀ (SC.f.app (op n))) (zero_add 0)) (add_zero 0) := by
          rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, SC.f.naturality]
      _ = (w'.comp (Ext.mk₀ (SC.X₁.map (homOfLE hk).op)) (add_zero 0)).comp
            (Ext.mk₀ (SC.f.app (op n))) (add_zero 0) :=
          (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm
      _ = (w.comp (Ext.mk₀ (SC.X₁.map (homOfLE hm).op)) (add_zero 0)).comp
            (Ext.mk₀ (SC.f.app (op n))) (add_zero 0) :=
          congrArg (fun t : Ext Z (SC.X₁.obj (op n)) 0 ↦
            t.comp (Ext.mk₀ (SC.f.app (op n))) (add_zero 0)) hw''
      _ = w.comp ((Ext.mk₀ (SC.X₁.map (homOfLE hm).op)).comp
            (Ext.mk₀ (SC.f.app (op n))) (zero_add 0)) (add_zero 0) :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = w.comp ((Ext.mk₀ (SC.f.app (op m))).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE hm).op)) (zero_add 0)) (add_zero 0) := by
          rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, SC.f.naturality]
      _ = (w.comp (Ext.mk₀ (SC.f.app (op m))) (add_zero 0)).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE hm).op)) (add_zero 0) :=
          (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm
      _ = b.comp (Ext.mk₀ (SC.X₂.map (homOfLE hm).op)) (add_zero 0) :=
          congrArg (fun t : Ext Z (SC.X₂.obj (op m)) 0 ↦
            t.comp (Ext.mk₀ (SC.X₂.map (homOfLE hm).op)) (add_zero 0)) hw
      _ = ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hm).op) b := rfl


end Main

end Ext
end Abelian
end CategoryTheory


theorem solution.{sol_u1, sol_u2, sol_u3} : type_of% @CategoryTheory.Abelian.Ext.exists_transition_preimage_ker.{sol_u1, sol_u2, sol_u3} := @CategoryTheory.Abelian.Ext.exists_transition_preimage_ker.{sol_u1, sol_u2, sol_u3}
